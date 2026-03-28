from pakages.trace_inference_rules.normalize_given_ontology_NoEdgeForRole import normalize
from pakages.trace_inference_rules.transform_class_NoEdgeForRole import transform_class
from pakages.trace_inference_rules.tools import delete_c, add_e, filter, tensor_prod

import json
import copy
import pickle
from tqdm import tqdm
import itertools
import time
import os


class clause():
    def __init__(self, conclu, premise):
        self.premise = premise
        self.conclu = conclu

    def premise(self):
        return self.premise

    def conclu(self):
        return self.conclu


class trace_inference():
    def __init__(self, path_ontology, name_ontology, initialize=False):
        self.name_ontology = name_ontology
        self.path_ontology = path_ontology
        start_time = time.time()
        
        preprocessing_path = os.path.join(self.path_ontology, 'data', 'preprocessing_results.json')
        
        if initialize:
            print(
                '\n\nnormalization ##################################################################################\n\n\n')
            self.num_concepts, l_concepts_part_orginal = normalize(self.path_ontology, self.name_ontology)
            print(self.num_concepts)

            print(
                '\n\nclassification new defined ontology ##################################################################\n\n\n')
            # calculate the class
            os.system(
                f'java -jar pakages/elk-tools/elk-standalone.jar -i pakages/elk-tools/{self.name_ontology}_normalized_new_defined.txt -c -o pakages/elk-tools/{self.name_ontology}.class')

            print(
                '\n\nbuild hyper-graph and S_A ##################################################################################\n\n\n')
            # calculate S_X, and the hyper-graph
            self.k_E_role = transform_class(self.path_ontology, self.name_ontology, self.num_concepts,
                                            l_concepts_part_orginal)

            print(self.k_E_role)

            print('\n\n##################################################################################\n')
            print(f'preprocessing step finished in {time.time() - start_time}')

            preprocessing_data = {
                'num_concepts': self.num_concepts,
                'k_E_role': self.k_E_role
            }
            with open(preprocessing_path, 'w') as f:
                json.dump(preprocessing_data, f)
            print(f'Preprocessing results saved to {preprocessing_path}')

            print('loading data........')
        else:
            if os.path.exists(preprocessing_path):
                with open(preprocessing_path, 'r') as f:
                    preprocessing_data = json.load(f)
                self.num_concepts = preprocessing_data['num_concepts']
                self.k_E_role = preprocessing_data['k_E_role']
                print(f'Preprocessing results loaded from {preprocessing_path}')
            else:
                raise FileNotFoundError(f'Preprocessing results not found at {preprocessing_path}. Please run with initialize=True first.')

        print("count_c,self.k_E_role:", self.num_concepts, self.k_E_role)

        # cwd = os.getcwd()  # Get the current working directory (cwd)
        # files = os.listdir(cwd)  # Get all the files in that directory
        # print("Files in %r: %s" % (cwd, files))

        with open('{}data/indE2id_original_axiom.json'.format(self.path_ontology), 'r') as f:
            self.indE2id_original_axiom = json.load(f)
        with open('{}data/{}_concept2id.json'.format(self.path_ontology, self.name_ontology), 'r') as f:
            self.concepts2id = json.load(f)
        with open('{}data/E.json'.format(self.path_ontology), 'r') as f:
            self.E = json.load(f)
        with open('{}data/E_R.json'.format(self.path_ontology), 'r') as f:
            self.E_R = json.load(f)
        with open('{}data/D_edge.json'.format(self.path_ontology), 'r') as f:
            self.D_edge = json.load(f)  # key:str, value: list of int
        with open('{}data/M_r_A_inverse.pickle'.format(self.path_ontology), 'rb') as f:
            self.M_inverse = pickle.load(f)
        with open('{}data/M_r_A_appear.pickle'.format(self.path_ontology), 'rb') as f:
            self.M = pickle.load(f)
        with open('{}data/M_R.pickle'.format(self.path_ontology), 'rb') as f:
            self.M_R = pickle.load(f)
        with open('{}data/dic_t_r.pickle'.format(self.path_ontology), 'rb') as f:
            self.dic_t_r = pickle.load(f)
        with open('{}data/dic_tr_s.pickle'.format(self.path_ontology), 'rb') as f:
            self.dic_tr_s = pickle.load(f)
        with open('{}data/a2a_n.pickle'.format(self.path_ontology), 'rb') as f:
            self.a2a_n = pickle.load(f)
        with open('{}data/dic_tr_s_original.pickle'.format(self.path_ontology), 'rb') as f:
            self.dic_tr_s_original = pickle.load(f)

        self.D_node = set([str(a) for a in self.D_edge])

        self.trs2id = {}
        count_trs2id = 0
        for (t, r) in self.dic_tr_s_original:
            for s in self.dic_tr_s_original[t, r]:
                self.trs2id[(r, s, t)] = 'c' + str(count_trs2id)
                self.indE2id_original_axiom['c' + str(count_trs2id)] = 'c' + str(count_trs2id)
                count_trs2id += 1
        print('ontology preprocessing data loaded in {}'.format(time.time() - start_time))

        self.current_result, self.initial_result = {}, {}
        self.unfold_pair = set([])
        self.rules_appear = []
        self.loop_pair = set([])
        self.current_pair_s = set([])
        self.invalid_pairs = set([])
        self.rules2id, self.count_id = {}, 2

        self.r2c_history = {}
        self.seperate_2_history = {}
        self.normal_path_history = {}
        self.normal_path_role_history = {}

    def filter_role_path(self, path):
        for p in path:
            if [a for a in p if int(a) < self.k_E_role]:
                return True
        return False

    def get_r2c(self, n):
        if n in self.r2c_history:
            return self.r2c_history[n]

        result = {}
        for a in self.M_inverse[n]:  # a = k*num_concept+k_r
            r = int(a) // self.num_concepts
            if r > 0:
                r_A = int(a) % self.num_concepts
                if r in result:
                    result[r].add(r_A)
                else:
                    result[r] = {r_A}
        self.r2c_history[n] = result
        return result

    def last_part_1(self, n, m, c1=None):
        assert int(m) < self.num_concepts
        if n == m:
            return True
        if m in self.D_edge:  # see here **
            return True
        p1 = self.normal_paths(n, m)
        if p1:
            if c1:
                p1 = delete_c(p1, c1)
            if p1:
                return True

        mid = self.M[m] & self.M_inverse[n]
        mid_definite = mid & self.D_node
        for i in mid_definite:
            assert str(i) != m  # in this case,see ** above
            if str(i) != n:
                path_2_original = self.normal_paths(str(i), m)
                for d_edge in self.D_edge[str(i)]:
                    if int(m) in d_edge[2:]:
                        pass
                    else:
                        path_2 = delete_c(path_2_original, c=d_edge[0])
                        if not path_2:
                            continue
                        else:
                            if c1:
                                path_2 = delete_c(path_2, c1)
                            if path_2:
                                return True

        for a in mid:
            k = int(a) // self.num_concepts
            if k <= 0:
                pass
            else:
                p = self.normal_paths(a, m)
                if p:
                    if not self.filter_role_path(p):
                        print('last_part_1:', n, a, m)
                    assert self.filter_role_path(p)
                if p:
                    if c1:
                        p = delete_c(p, c1)
                        if p:
                            return True
                    else:
                        return True
        return False

    def seperate_2(self, n, m):
        if n + ' ' + m in self.seperate_2_history:
            return self.seperate_2_history[n + ' ' + m]

        mid = self.M[m] & self.M_inverse[n]
        assert len(mid) >= 2
        mid_definite = mid & self.D_node
        if len(mid) < 3 and int(m) < self.num_concepts:
            self.seperate_2_history[n + ' ' + m] = (mid_definite, [], [])
            return mid_definite, [], []

        t2c_start = self.get_r2c(n)

        t2c_end_0 = {}
        t2c_end = {}
        for a in mid:
            k = int(a) // self.num_concepts
            if k <= 0:
                pass
            else:
                k_r = int(a) % self.num_concepts
                if self.normal_paths(a, m) or a == m:
                    if k in t2c_end:
                        t2c_end[k].add(k_r)
                    else:
                        t2c_end[k] = {k_r}
                    if self.filter_role_path(self.normal_paths(a, m)) or a == m:
                        if k in t2c_end_0:
                            t2c_end_0[k].add(k_r)
                        else:
                            t2c_end_0[k] = {k_r}

        all_pairs = []
        for t2 in t2c_end_0:
            for t1 in self.M_R[t2] & t2c_start.keys():
                for l2 in t2c_end_0[t2]:
                    if str(l2 + t2 * self.num_concepts) == m:
                        continue
                    for l1 in t2c_start[t1]:
                        if l2 != l1 and str(l1) in self.M[str(l2)]:
                            if t1 != t2:
                                all_pairs.append(
                                    [n + '\t' + str(l1 + t1 * self.num_concepts), str(l1) + '\t' + str(l2),
                                     'E' + str(l2 + t2 * self.num_concepts) + '\t' + m, (str(t1), str(t2))])
                            else:
                                all_pairs.append(
                                    [n + '\t' + str(l1 + t1 * self.num_concepts), str(l1) + '\t' + str(l2),
                                     'E' + str(l2 + t2 * self.num_concepts) + '\t' + m])

        Three_pair = []
        for (t1, r1) in self.dic_tr_s:
            if t1 in t2c_end:
                r_avliable = self.dic_t_r[t1] & self.M_R[r1] & t2c_start.keys()
                if r_avliable:
                    S_s = self.dic_tr_s[t1, r1]
                    for r in r_avliable:
                        for C, D in itertools.product(t2c_start[r], t2c_end[t1]):
                            n_C = str(C + r * self.num_concepts)
                            for s_A, s in {(s_A, int(s_A) // self.num_concepts) for s_A in self.M_inverse[str(C)] if
                                           int(s_A) % self.num_concepts == D and int(
                                               s_A) // self.num_concepts in S_s}:
                                if str(D + t1 * self.num_concepts) == m:
                                    Three_pair.append([n + '\t' + n_C, str(C) + '\t' + s_A, (r, s, t1)])
                                else:
                                    Three_pair.append([n + '\t' + n_C, str(C) + '\t' + s_A,
                                                       'E' + str(D + t1 * self.num_concepts) + '\t' + m,
                                                       (r, s, t1)])
        self.seperate_2_history[n + ' ' + m] = (mid_definite, all_pairs, Three_pair)
        return mid_definite, all_pairs, Three_pair

    def normal_paths(self, n, m):
        if n + '\t' + m in self.normal_path_history:
            return self.normal_path_history[n + '\t' + m]
        if n == m:
            return []
        result = []
        current_path = ['s']
        visited = [int(n)]
        mid = self.M[m] & self.M_inverse[n]
        if len(mid) < 2:
            print(n, m)
            assert 1 == 0
        E_extract = self.trans(mid)

        avaliable_edges = []
        new_edge = []
        if n in E_extract.keys():
            new_edge += E_extract[n]

        n_r, n_rest = str(int(n) // self.num_concepts), int(n) % self.num_concepts
        if n_r in self.E_R:
            new_edge += self.addrest(self.E_R[n_r], n_rest)

        if not new_edge:
            self.normal_path_history[n + '\t' + m] = []
            return []

        avaliable_edges.append(copy.deepcopy(new_edge))
        while True:
            if not avaliable_edges[-1]:
                avaliable_edges.pop()
                current_path.pop()
                visited.pop()
                if not avaliable_edges:
                    break
                else:
                    continue
            # prevent infinite loops
            if avaliable_edges[-1][-1][-1] not in visited:
                next_node = avaliable_edges[-1][-1][-1]
                if str(next_node) == m:
                    result.append(current_path[1:] + [avaliable_edges[-1][-1][0]])
                    avaliable_edges[-1][-1].pop()
                    if len(avaliable_edges[-1][-1]) == 2:
                        avaliable_edges[-1].pop()
                else:
                    next_node_r = str(int(next_node) // self.num_concepts)
                    if str(next_node) not in E_extract.keys() and next_node_r not in self.E_R:
                        avaliable_edges[-1][-1].pop()
                        if len(avaliable_edges[-1][-1]) == 2:
                            avaliable_edges[-1].pop()
                        continue
                    else:
                        current_path.append(avaliable_edges[-1][-1][0])
                        visited.append(next_node)
                        avaliable_edges[-1][-1].pop()
                        if len(avaliable_edges[-1][-1]) == 2:
                            avaliable_edges[-1].pop()

                        new_edge = []
                        if str(next_node) in E_extract:
                            new_edge += E_extract[str(next_node)]
                        if next_node_r in self.E_R:
                            new_edge += self.addrest(self.E_R[next_node_r], int(next_node) % self.num_concepts)
                        avaliable_edges.append(copy.deepcopy(new_edge))
            else:
                avaliable_edges[-1][-1].pop()
                if len(avaliable_edges[-1][-1]) == 2:
                    avaliable_edges[-1].pop()
                continue
        if not result:
            self.normal_path_history[n + '\t' + m] = []
            return []
        else:
            self.normal_path_history[n + '\t' + m] = [set(p) for p in result]
            return [set(p) for p in result]

    def normal_paths_role(self, r, s):
        assert int(r) in self.M_R[int(s)]
        if (r, s) in self.normal_path_role_history:
            return self.normal_path_role_history[r, s]
        if r == s:
            return []
        result = []
        current_path = ['s']
        visited = [r]
        if r in self.E_R.keys():
            avaliable_edges = [copy.deepcopy(self.E_R[r])]
        else:
            self.normal_path_history[r, s] = []
            return []
        while True:
            if not avaliable_edges[-1]:
                avaliable_edges.pop()
                current_path.pop()
                visited.pop()
                if not avaliable_edges:
                    break
                else:
                    continue
            if avaliable_edges[-1][-1][-1] not in visited:
                next_node = avaliable_edges[-1][-1][-1]
                if next_node == s:
                    result.append(current_path[1:] + [avaliable_edges[-1][-1][0]])
                    avaliable_edges[-1][-1].pop()
                    if len(avaliable_edges[-1][-1]) == 2:
                        avaliable_edges[-1].pop()
                else:
                    if str(next_node) not in self.E_R.keys():
                        avaliable_edges[-1][-1].pop()
                        if len(avaliable_edges[-1][-1]) == 2:
                            avaliable_edges[-1].pop()
                        continue
                    else:
                        current_path.append(avaliable_edges[-1][-1][0])
                        visited.append(next_node)
                        avaliable_edges[-1][-1].pop()
                        if len(avaliable_edges[-1][-1]) == 2:
                            avaliable_edges[-1].pop()
                        new_edge = copy.deepcopy(self.E_R[next_node])
                        avaliable_edges.append(new_edge)
            else:
                avaliable_edges[-1][-1].pop()
                if len(avaliable_edges[-1][-1]) == 2:
                    avaliable_edges[-1].pop()
                continue
        self.normal_path_role_history[r, s] = [set(p) for p in result]
        return [set(p) for p in result]

    def addrest(self, E, rest):
        result = []
        for e in E:
            e_new = e[:2]
            for n in e[2:]:
                e_new.append(int(n) * self.num_concepts + rest)
            result.append(e_new)

        return result

    def just_object_chain(self, r, s, t):
        result = []
        for t1, r1 in self.dic_tr_s_original:
            if t1 == t:
                if r in self.M_R[r1]:
                    result_1 = self.normal_paths_role(str(r), str(r1))
                    for s1 in self.dic_tr_s_original[t1, r1]:
                        if s in self.M_R[s1]:
                            result_1 = tensor_prod(result_1, self.normal_paths_role(str(s), str(s1)))
                            if not result_1:
                                result.append({self.trs2id[r1, s1, t1]})
                            else:
                                result += add_e(result_1, self.trs2id[r1, s1, t1])
        return filter(result)

    def trans(self, mid):
        E_extract = {}
        for node in mid:
            result = []
            if str(node) not in self.E.keys():
                continue
            for edge in self.E[str(node)]:
                joint = [edge[i] for i in range(len(edge)) if i < 2 or str(edge[i]) in mid]
                if len(joint) > 2:
                    result.append(joint)
            if result:
                E_extract[node] = copy.deepcopy(result)
        return E_extract

    def just_rule_ordered(self, n, m):
        assert n in self.M[m]
        if n == m or n + '\t' + m in self.invalid_pairs:
            return False
        self.unfold_pair.add(n + '\t' + m)
        self.current_pair_s.add(n + '\t' + m)

        mid_definite, seperate_pairs, three_pairs = self.seperate_2(n, m)

        result_1 = self.normal_paths(n, m)
        if result_1:
            self.initial_result[n + '\t' + m] = result_1

        f_split_vaid = True
        for i in mid_definite:
            if i == n:
                continue
            path_2_original = self.normal_paths(str(i), m)
            for id_edge, d_edge in enumerate(self.D_edge[str(i)]):
                if int(m) in d_edge[2:]:
                    continue
                if str(i) != m:
                    path_2 = delete_c(path_2_original, c=d_edge[0])
                    if not path_2:
                        continue

                flag = False
                for i_pre in d_edge[2:]:
                    path_d = self.last_part_1(n, str(i_pre), c1=d_edge[0])
                    if not path_d:
                        flag = True
                        break

                if not flag:
                    f_split_vaid = False
                    premise_i = {n + '\t' + str(pre_node) for pre_node in d_edge[2:] if str(pre_node) != n}
                    if str(i) != m:
                        premise_i.add('S' + str(i) + '\t' + m + '\t' + str(id_edge))
                        self.initial_result['S' + str(i) + '\t' + m + '\t' + str(id_edge)] = add_e(path_2, d_edge[0])
                        self.generate_clause(n + '\t' + m, premise_i)
                    else:
                        premise_i.add(d_edge[0])
                        self.initial_result[d_edge[0]] = []
                        self.generate_clause(n + '\t' + m, premise_i)

                    for pre_node in d_edge[2:]:
                        if n + '\t' + str(pre_node) in self.current_pair_s:
                            self.loop_pair.add(n + '\t' + str(pre_node))
                        elif n + '\t' + str(pre_node) not in self.unfold_pair:
                            f_a = self.just_rule_ordered(n, str(pre_node))
                            assert f_a or n == str(pre_node)

        for pairs in seperate_pairs:
            for j in [0, 1]:
                if pairs[j] in self.current_pair_s:
                    self.loop_pair.add(pairs[j])
                elif pairs[j] not in self.unfold_pair:
                    li = pairs[j].split('\t')
                    if j == 0:
                        if not self.just_rule_ordered(li[0], li[1]):
                            self.invalid_pairs.add(pairs[0])
                            break
                    else:
                        f_a = self.just_rule_ordered(li[0], li[1])
                        assert f_a or li[0] == li[1]
            else:
                f_split_vaid = False
                if len(pairs) == 4:
                    self.initial_result[pairs[-1]] = self.normal_paths_role(pairs[-1][0], pairs[-1][1])
                    l_id = -2
                else:
                    l_id = -1
                l = pairs[l_id][1:].split('\t')
                self.initial_result[pairs[2]] = self.normal_paths(l[0], l[1])
                assert self.initial_result[pairs[2]]
                self.generate_clause(n + '\t' + m, set(pairs))

        for pairs in three_pairs:
            for p in pairs[:2]:
                if p in self.current_pair_s:
                    self.loop_pair.add(p)
                elif p not in self.unfold_pair:
                    lp = p.split('\t')
                    if not self.just_rule_ordered(lp[0], lp[1]):
                        self.invalid_pairs.add(p)
                        break
            else:
                f_split_vaid = False
                l_last = pairs[-2][1:].split('\t')
                if len(pairs) == 4:
                    self.initial_result[pairs[-2]] = self.normal_paths(l_last[0], l_last[1])
                self.initial_result[pairs[-1]] = self.just_object_chain(pairs[-1][0], pairs[-1][1], pairs[-1][2])
                self.generate_clause(n + '\t' + m, set(pairs))

        self.current_pair_s.remove(n + '\t' + m)
        if not result_1 and f_split_vaid:
            return False
        else:
            return True

    def generate_clause(self, k, premise):
        self.rules_appear.append(clause(k, premise))
        return

    def mapback(self, S):
        result = []
        for p in S:
            new_p = {self.indE2id_original_axiom[str(e)] for e in p if str(e) in self.indE2id_original_axiom}
            if new_p:
                result.append(new_p)
        return filter(result)

    def setid_rules2id(self, k_orginal):
        if isinstance(k_orginal, dict):
            k = str(k_orginal)
        elif isinstance(k_orginal, list):
            for ki in k_orginal:
                assert isinstance(ki, dict)
            k = [str(ki) for ki in k_orginal]
        else:
            k = k_orginal

        if k not in self.rules2id:
            self.rules2id[k] = str(self.count_id)
            self.count_id += 1
        return self.rules2id[k]

    def transfer2idForm(self):
        result, s_a = {}, set([])

        valid_initial_terms = set([])
        for k in self.initial_result:
            if not self.initial_result[k]:
                continue
            result_k_mapback = self.mapback(self.initial_result[k])
            if not result_k_mapback:
                valid_initial_terms.add(k)
                continue

            for p in result_k_mapback:
                con_id = self.setid_rules2id(k)
                pre_ids = []
                for e in p:
                    e_id = self.setid_rules2id(e)
                    pre_ids.append(e_id)
                    s_a.add(int(e_id))

                if con_id in result:
                    result[con_id].append(pre_ids)
                else:
                    result[con_id] = [pre_ids]

        for r in self.rules_appear:
            if r.premise & self.invalid_pairs:
                continue

            con_id = self.setid_rules2id(r.conclu)
            pre_ids = []
            for pre in r.premise:
                if pre in valid_initial_terms:
                    continue
                if pre in self.initial_result and not self.initial_result[pre]:
                    if str(pre) in self.indE2id_original_axiom:
                        id_pre = self.setid_rules2id(self.indE2id_original_axiom[str(pre)])
                        s_a.add(int(id_pre))
                        pre_ids.append(id_pre)
                else:
                    id_pre = self.setid_rules2id(pre)
                    pre_ids.append(id_pre)

            if con_id in result:
                result[con_id].append(pre_ids)
            else:
                result[con_id] = [pre_ids]

        for term in self.rules2id.keys() & self.a2a_n.keys():
            assert isinstance(term, int)
            id_term = self.setid_rules2id(term)
            set_term_n = self.a2a_n[term] & self.rules2id.keys()
            if set_term_n:
                s_a.remove(int(id_term))
                new_term = self.setid_rules2id('duplicate' + str(term))
                if id_term not in result:
                    result[id_term].append([new_term])
                else:
                    result[id_term] = [[new_term]]

                for term_n in set_term_n:
                    id_term_n = self.setid_rules2id(term_n)
                    if id_term not in result:
                        result[id_term].append([id_term_n])
                    else:
                        result[id_term] = [[id_term_n]]

                s_a.add(int(new_term))

        return result, s_a

    def clear_trace_data(self):
        self.current_result, self.initial_result = {}, {}
        self.unfold_pair = set([])
        self.rules_appear = []
        self.loop_pair = set([])
        self.current_pair_s = set([])
        self.invalid_pairs = set([])
        self.rules2id, self.count_id = {}, 2

        self.r2c_history = {}
        self.seperate_2_history = {}
        self.normal_path_history = {}
        self.normal_path_role_history = {}

    def trace_inference_rules(self, test_sample_direct, type='not_indexed'):
        goal_id = []
        for pair in tqdm(test_sample_direct):
            if type == 'not_indexed':
                id1, id2 = str(self.concepts2id[pair[0]]), str(self.concepts2id[pair[1]])
            else:
                id1, id2 = pair[0], pair[1]
            ind_goal = self.setid_rules2id(id1 + '\t' + id2)
            goal_id.append(ind_goal)
            self.just_rule_ordered(id1, id2)

        new_result, s_a = self.transfer2idForm()

        print('finished!')
        return new_result, s_a, goal_id


if __name__ == "__main__":
    # !!!!!! we need use protege make the terminology is with declaration !!!!!!
    # path_ontology, name_ontology = "workspace/galen7", 'terminologyWithDeclaration'
    path_ontology, name_ontology = 'workspace/snomedct2021_snapshot/', 'terminologyWithDeclaration'
    count_c, k_E_role = None, None
    # count_c, k_E_role =  38579, 53188
    # test_sample = []
    # with open(f'{path_ontology}/queries_terminology', 'r') as f:
    #     data = f.readlines()
    #     for row in tqdm(data):
    #         test_sample.append(row[:-1].split('\t'))

    test = trace_inference(path_ontology, name_ontology, count_c, k_E_role)
    test_sample=[("26035", "285909")]
    # test_sample = [["galen7.owl#Existentiality", "galen7.owl#ModifierConcept"]]
    test.trace_inference_rules(test_sample)
