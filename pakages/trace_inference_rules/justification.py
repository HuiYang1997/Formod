import json
import copy
import time
import pickle
from tqdm import tqdm
from tools import delete_c, add_e, mkdir, filter, tensor_prod
import itertools
import numpy as np


def just(name_ontology, num_concepts, k_E_role, l=-1):
    current_result, initial_result = {}, {}

    start_time = time.time()
    print('loading data........')
    with open('workspace/{}/data/indE2id_original_axiom.json'.format(name_ontology), 'r') as f:
        indE2id_original_axiom = json.load(f)
    with open('workspace/{}/data/{}_concept2id.json'.format(name_ontology, name_ontology), 'r') as f:
        concepts2id = json.load(f)
    test_sample_direct = []
    with open(f'workspace/{name_ontology}/queries_test', 'r') as f:
        data = f.readlines()
        # have form 'Declaration(Class(<#D121>))' or 'SubClassOf(<#c25665> <#N2301>)' or 'EquivalentClasses(<#N2304> <#c15112>)'
        # have form: "#query_id (implies #... (some #... #...))", or "#query_id (implies #... #...)" or query_id (implies (some #... #...) ... )
        for row in tqdm(data):
            #test_sample_direct.append(row[:-1].replace('id/','').split(' '))
            test_sample_direct.append([concepts2id[c] for c in row[:-1].split(' ')])
    #test_sample_direct = [['2072', '5790']]
    with open('workspace/{}/data/E.json'.format(name_ontology), 'r') as f:
        E = json.load(f)
    with open('workspace/{}/data/E_R.json'.format(name_ontology), 'r') as f:
        E_R = json.load(f)
    with open('workspace/{}/data/D_edge.json'.format(name_ontology), 'r') as f:
        D_edge = json.load(f)  # key:str, value: list of int
    with open('workspace/{}/data/M_r_A_inverse.pickle'.format(name_ontology), 'rb') as f:
        M_inverse = pickle.load(f)
    with open('workspace/{}/data/M_r_A_appear.pickle'.format(name_ontology), 'rb') as f:
        M = pickle.load(f)
    with open('workspace/{}/data/M_R.pickle'.format(name_ontology), 'rb') as f:
        M_R = pickle.load(f)
    with open('workspace/{}/data/dic_t_r.pickle'.format(name_ontology), 'rb') as f:
        dic_t_r = pickle.load(f)
    with open('workspace/{}/data/dic_tr_s.pickle'.format(name_ontology), 'rb') as f:
        dic_tr_s = pickle.load(f)
    with open('workspace/{}/data/a2a_n.pickle'.format(name_ontology), 'rb') as f:
        a2a_n = pickle.load(f)
    with open('workspace/{}/data/dic_tr_s_original.pickle'.format(name_ontology), 'rb') as f:
        dic_tr_s_original = pickle.load(f)

    D_node = set([str(a) for a in D_edge])

    trs2id = {}
    count_trs2id = 0
    for (t, r) in dic_tr_s_original:
        for s in dic_tr_s_original[t, r]:
            trs2id[(r, s, t)] = 'c' + str(count_trs2id)
            indE2id_original_axiom['c' + str(count_trs2id)] = 'c' + str(count_trs2id)
            count_trs2id += 1
    print('all preprocessing data loaded in {}'.format(time.time() - start_time))

    def_AND_nor_history = {}

    def filter_role_path(path):
        for p in path:
            if [a for a in p if int(a) < k_E_role]:
                return True
        return False

    r2c_history = {}

    def get_r2c(n):
        nonlocal r2c_history
        if n in r2c_history:
            return r2c_history[n]

        result = {}
        for a in M_inverse[n]:  # a = k*num_concept+k_r
            r = int(a) // num_concepts
            if r > 0:
                r_A = int(a) % num_concepts
                if r in result:
                    result[r].add(r_A)
                else:
                    result[r] = {r_A}
        r2c_history[n] = result
        return result

    def last_part_1(n, m, c1=None):
        assert int(m) < num_concepts
        if n == m:
            return True
        if m in D_edge:  # see here **
            return True
        p1 = normal_paths(n, m)
        if p1:
            if c1:
                p1 = delete_c(p1, c1)
            if p1:
                return True

        mid = M[m] & M_inverse[n]
        mid_definite = mid & D_node
        for i in mid_definite:
            assert str(i) != m  # in this case,see ** above
            if str(i) != n:
                path_2_original = normal_paths(str(i), m)
                for d_edge in D_edge[str(i)]:
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
            k = int(a) // num_concepts
            if k <= 0:
                pass
            else:
                p = normal_paths(a, m)
                if p:
                    if not filter_role_path(p):
                        print('last_part_1:', n, a, m)
                    assert filter_role_path(p)
                if p:
                    if c1:
                        p = delete_c(p, c1)
                        if p:
                            return True
                    else:
                        return True
        return False

    seperate_2_history = {}

    def seperate_2(n, m):
        if n + ' ' + m in seperate_2_history:
            return seperate_2_history[n + ' ' + m]

        mid = M[m] & M_inverse[n]
        assert len(mid) >= 2
        mid_definite = mid & D_node
        if len(mid) < 3 and int(m) < num_concepts:
            seperate_2_history[n + ' ' + m] = (mid_definite, [], [])
            return mid_definite, [], []

        t2c_start = get_r2c(n)

        t2c_end_0 = {}
        t2c_end = {}
        for a in mid:
            k = int(a) // num_concepts
            if k <= 0:
                pass
            else:
                k_r = int(a) % num_concepts
                if normal_paths(a, m) or a == m:
                    if k in t2c_end:
                        t2c_end[k].add(k_r)
                    else:
                        t2c_end[k] = {k_r}
                    if filter_role_path(normal_paths(a,m)) or a == m:
                        if k in t2c_end_0:
                            t2c_end_0[k].add(k_r)
                        else:
                            t2c_end_0[k] = {k_r}

        all_pairs = []
        for t2 in t2c_end_0:
            for t1 in M_R[t2] & t2c_start.keys():
                for l2 in t2c_end_0[t2]:
                    if str(l2 + t2 * num_concepts) == m:
                        continue
                    for l1 in t2c_start[t1]:
                        if l2 != l1 and str(l1) in M[str(l2)]:
                            if t1 != t2:
                                all_pairs.append([n + '\t' + str(l1 + t1 * num_concepts), str(l1) + '\t' + str(l2),
                                                  'E' + str(l2 + t2 * num_concepts) + '\t' + m, (str(t1), str(t2))])
                            else:
                                all_pairs.append([n + '\t' + str(l1 + t1 * num_concepts), str(l1) + '\t' + str(l2),
                                                  'E' + str(l2 + t2 * num_concepts) + '\t' + m])

        Three_pair = []
        for (t1, r1) in dic_tr_s:
            if t1 in t2c_end:
                r_avliable = dic_t_r[t1] & M_R[r1] & t2c_start.keys()
                if r_avliable:
                    S_s = dic_tr_s[t1, r1]
                    for r in r_avliable:
                        for C, D in itertools.product(t2c_start[r], t2c_end[t1]):
                            n_C = str(C + r * num_concepts)
                            for s_A, s in {(s_A, int(s_A) // num_concepts) for s_A in M_inverse[str(C)] if
                                           int(s_A) % num_concepts == D and int(s_A) // num_concepts in S_s}:
                                if str(D + t1 * num_concepts) == m:
                                    Three_pair.append([n + '\t' + n_C, str(C) + '\t' + s_A, (r, s, t1)])
                                else:
                                    Three_pair.append([n + '\t' + n_C, str(C) + '\t' + s_A,
                                                       'E' + str(D + t1 * num_concepts) + '\t' + m, (r, s, t1)])
        seperate_2_history[n + ' ' + m] = (mid_definite, all_pairs, Three_pair)
        return mid_definite, all_pairs, Three_pair

    normal_path_history = {}

    def normal_paths(n, m):
        nonlocal normal_path_history, E_R
        if n + '\t' + m in normal_path_history:
            return normal_path_history[n + '\t' + m]
        if n == m:
            return []
        result = []
        current_path = ['s']
        visited = [int(n)]
        mid = M[m] & M_inverse[n]
        if len(mid) < 2:
            print(n, m)
            assert 1 == 0
        E_extract = trans(mid)

        avaliable_edges = []
        new_edge = []
        if n in E_extract.keys():
            new_edge += E_extract[n]
        n_r, n_rest = str(int(n) // num_concepts), int(n) % num_concepts
        if n_r in E_R:
            new_edge += addrest(E_R[n_r], n_rest)

        if not new_edge:
            normal_path_history[n + '\t' + m] = []
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
                    next_node_r = str(int(next_node) // num_concepts)
                    if str(next_node) not in E_extract.keys() and next_node_r not in E_R:
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
                        if next_node_r in E_R:
                            new_edge += addrest(E_R[next_node_r], int(next_node) % num_concepts)
                        avaliable_edges.append(copy.deepcopy(new_edge))
            else:
                avaliable_edges[-1][-1].pop()
                if len(avaliable_edges[-1][-1]) == 2:
                    avaliable_edges[-1].pop()
                continue
        if not result:
            normal_path_history[n + '\t' + m] = []
            return []
        else:
            normal_path_history[n + '\t' + m] = [set(p) for p in result]
            return [set(p) for p in result]

    normal_path_role_history = {}

    def normal_paths_role(r, s):
        nonlocal normal_path_role_history
        assert int(r) in M_R[int(s)]
        if (r, s) in normal_path_role_history:
            return normal_path_role_history[r, s]
        if r == s:
            return []
        result = []
        current_path = ['s']
        visited = [r]
        if r in E_R.keys():
            avaliable_edges = [copy.deepcopy(E_R[r])]
        else:
            normal_path_history[r, s] = []
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
                    if str(next_node) not in E_R.keys():
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
                        new_edge = copy.deepcopy(E_R[next_node])
                        avaliable_edges.append(new_edge)
            else:
                avaliable_edges[-1][-1].pop()
                if len(avaliable_edges[-1][-1]) == 2:
                    avaliable_edges[-1].pop()
                continue
        normal_path_role_history[r, s] = [set(p) for p in result]
        return [set(p) for p in result]

    def addrest(E, rest):
        result = []
        for e in E:
            e_new = e[:2]
            for n in e[2:]:
                e_new.append(int(n) * num_concepts + rest)
            result.append(e_new)

        return result

    def just_object_chain(r, s, t):
        result = []
        for t1, r1 in dic_tr_s_original:
            if t1 == t:
                if r in M_R[r1]:
                    result_1 = normal_paths_role(str(r), str(r1))
                    for s1 in dic_tr_s_original[t1, r1]:
                        if s in M_R[s1]:
                            result_1 = tensor_prod(result_1, normal_paths_role(str(s), str(s1)))
                            if not result_1:
                                result.append({trs2id[r1, s1, t1]})
                            else:
                                result += add_e(result_1, trs2id[r1, s1, t1])
        return filter(result)

    def trans(mid):
        E_extract = {}
        for node in mid:
            result = []
            if str(node) not in E.keys():
                continue
            for edge in E[str(node)]:
                joint = [edge[i] for i in range(len(edge)) if i < 2 or str(edge[i]) in mid]
                if len(joint) > 2:
                    result.append(joint)
            if result:
                E_extract[node] = copy.deepcopy(result)
        return E_extract

    unfold_pair = set([])
    rules_appear = []
    loop_pair = set([])
    current_pair_s = set([])
    invalid_pairs = set([])

    def just_rule_ordered(n, m):
        nonlocal unfold_pair, current_pair_s, loop_pair, D_edge, initial_result, invalid_pairs
        assert n in M[m]
        if n == m or n + '\t' + m in invalid_pairs:
            return False
        unfold_pair.add(n + '\t' + m)
        current_pair_s.add(n + '\t' + m)

        mid_definite, seperate_pairs, three_pairs = seperate_2(n, m)

        result_1 = normal_paths(n, m)
        if result_1:
            initial_result[n + '\t' + m] = result_1

        f_split_vaid = True
        for i in mid_definite:
            if i == n:
                continue
            path_2_original = normal_paths(str(i), m)
            for id_edge, d_edge in enumerate(D_edge[str(i)]):
                if int(m) in d_edge[2:]:
                    continue
                if str(i) != m:
                    path_2 = delete_c(path_2_original, c=d_edge[0])
                    if not path_2:
                        continue

                flag = False
                for i_pre in d_edge[2:]:
                    path_d = last_part_1(n, str(i_pre), c1=d_edge[0])
                    if not path_d:
                        flag = True
                        break

                if not flag:
                    f_split_vaid = False
                    premise_i = {n + '\t' + str(pre_node) for pre_node in d_edge[2:] if str(pre_node) != n}
                    if str(i) != m:
                        premise_i.add('S' + str(i) + '\t' + m + '\t' + str(id_edge))
                        initial_result['S' + str(i) + '\t' + m + '\t' + str(id_edge)] = add_e(path_2, d_edge[0])
                        generate_clause(n + '\t' + m, premise_i)
                    else:
                        premise_i.add(d_edge[0])
                        initial_result[d_edge[0]] = []
                        generate_clause(n + '\t' + m, premise_i)

                    for pre_node in d_edge[2:]:
                        if n + '\t' + str(pre_node) in current_pair_s:
                            loop_pair.add(n + '\t' + str(pre_node))
                        elif n + '\t' + str(pre_node) not in unfold_pair:
                            f_a = just_rule_ordered(n, str(pre_node))
                            assert f_a or n == str(pre_node)

        for pairs in seperate_pairs:
            for j in [0, 1]:
                if pairs[j] in current_pair_s:
                    loop_pair.add(pairs[j])
                elif pairs[j] not in unfold_pair:
                    li = pairs[j].split('\t')
                    if j == 0:
                        if not just_rule_ordered(li[0], li[1]):
                            invalid_pairs.add(pairs[0])
                            break
                    else:
                        f_a = just_rule_ordered(li[0], li[1])
                        assert f_a or li[0] == li[1]
            else:
                f_split_vaid = False
                if len(pairs) == 4:
                    initial_result[pairs[-1]] = normal_paths_role(pairs[-1][0], pairs[-1][1])
                    l_id = -2
                else:
                    l_id = -1
                l = pairs[l_id][1:].split('\t')
                initial_result[pairs[2]] = normal_paths(l[0], l[1])
                assert initial_result[pairs[2]]
                generate_clause(n + '\t' + m, set(pairs))

        for pairs in three_pairs:
            for p in pairs[:2]:
                if p in current_pair_s:
                    loop_pair.add(p)
                elif p not in unfold_pair:
                    lp = p.split('\t')
                    if not just_rule_ordered(lp[0], lp[1]):
                        invalid_pairs.add(p)
                        break
            else:
                f_split_vaid = False
                l_last = pairs[-2][1:].split('\t')
                if len(pairs) == 4:
                    initial_result[pairs[-2]] = normal_paths(l_last[0], l_last[1])
                initial_result[pairs[-1]] = just_object_chain(pairs[-1][0], pairs[-1][1], pairs[-1][2])
                generate_clause(n + '\t' + m, set(pairs))

        current_pair_s.remove(n + '\t' + m)
        if not result_1 and f_split_vaid:
            return False
        else:
            return True

    class clause():
        def __init__(self, conclu, premise):
            self.premise = premise
            self.conclu = conclu

        def premise(self):
            return self.premise

        def conclu(self):
            return self.conclu

    def generate_clause(k, premise):
        nonlocal rules_appear
        rules_appear.append(clause(k, premise))
        return

    def mapback(S):
        result = []
        for p in S:
            new_p = {indE2id_original_axiom[str(e)] for e in p if str(e) in indE2id_original_axiom}
            if new_p:
                result.append(new_p)
        return filter(result)

    rules2id, count_id = {}, 1

    def setid_rules2id(k):
        nonlocal rules2id, count_id
        if k not in rules2id:
            rules2id[k] = str(count_id)
            count_id += 1
        return rules2id[k]

    query_filtered = []
    total_num = []

    def query_doc(k_ini):
        nonlocal initial_result, rules_appear, query_filtered, total_num, invalid_pairs, rules2id

        if not rules_appear:
            return

        query_filtered.append('id/' + k_ini.replace('\t', ' id/') + '\n')
        k_ini_new = k_ini.replace('\t', 't')
        query_file = f'result/query_{name_ontology}/{k_ini_new}'
        mkdir(query_file)

        total_cnf = 0
        s_a = set([])
        valid_initial_terms = set([])
        f_cnf = open(f"{query_file}/encoding.cnf", 'w')
        for k in initial_result:
            if not initial_result[k]:
                continue
            result_k_mapback = mapback(initial_result[k])
            if not result_k_mapback:
                valid_initial_terms.add(k)
                continue

            for p in result_k_mapback:
                for e in p:
                    e_id = setid_rules2id(e)
                    f_cnf.write('-' + e_id + ' ')
                    s_a.add(int(e_id))
                f_cnf.write(setid_rules2id(k) + ' 0\n')
                total_cnf += 1

        for r in rules_appear:
            if r.premise & invalid_pairs:
                continue
            for pre in r.premise:
                if pre in valid_initial_terms:
                    continue
                if pre in initial_result and not initial_result[pre]:
                    if str(pre) in indE2id_original_axiom:
                        id_pre = setid_rules2id(indE2id_original_axiom[str(pre)])
                        s_a.add(int(id_pre))
                        f_cnf.write('-' + id_pre + ' ')
                else:
                    id_pre = setid_rules2id(pre)
                    f_cnf.write('-' + id_pre + ' ')
            f_cnf.write(setid_rules2id(r.conclu) + ' 0\n')
            total_cnf += 1



        for term in rules2id & a2a_n.keys():
            assert isinstance(term, int)
            id_term = setid_rules2id(term)
            set_term_n = a2a_n[term] & rules2id.keys()
            if set_term_n:
                s_a.remove(int(id_term))
                new_term = setid_rules2id('duplicate' + str(term))
                for term_n in set_term_n:
                    id_term_n = setid_rules2id(term_n)
                    f_cnf.write(f'-{id_term_n} {id_term} 0\n')
                f_cnf.write(f'-{new_term} {id_term} 0\n')
                #print('!')
                total_cnf +=1
                s_a.add(int(new_term))

        f_cnf.close()
        total_num.append(total_cnf)

        with open(f"{query_file}/encoding.assumptions", 'w') as f_a:
            f_a.write(' '.join([str(a) for a in sorted(list(s_a))]) + ' 0\n')

        with open(f"{query_file}/encoding.q", 'w') as f_q:
            f_q.write(setid_rules2id(k_ini.replace('t', '\t')) + '\n')

    if l < 0:
        l = len(test_sample_direct)

    num_rule = []
    time_table, total_time, i = [], 0, -1
    for pair in tqdm(test_sample_direct):
        # print(pair)
        i += 1
        if i < l:
            rules2id, count_id = {}, 1
            initial_result= {}
            loop_pair, unfold_pair, current_pair_s, rules_appear = set([]), set([]), set([]), []

            start_time_1 = time.time()
            just_rule_ordered(str(pair[0]), str(pair[1]))
            query_doc(str(pair[0]) + '\t' + str(pair[1]))
            time_table.append(time.time() - start_time_1)
            total_time += time_table[-1]
            num_rule.append(len(rules_appear))
            if num_rule[-1] == 0:
                total_num.append(len(normal_paths(str(pair[0]), str(pair[1]))))
    assert len(num_rule) == len(total_num)
    print('number of generate rules: max: ', max(num_rule), ' min: ', min(num_rule), ' mean:',
          np.mean(np.array(num_rule)), ' median:', np.median(np.array(num_rule)))
    print('after unfolded: max: ', max(total_num), ' min: ', min(total_num), ' mean:', np.mean(np.array(total_num)),
          ' median:', np.median(np.array(total_num)))
    with open(f'result/queries_test_filtered_{name_ontology}', 'w') as f:
        for q in query_filtered:
            f.write(q)
    with open(f'result/rules_statis_{name_ontology}.csv', 'w') as f:
        f.write('num_rules,num_rules_unfold, ration_original_devide_unfold\n')
        for i in range(len(num_rule)):
            if num_rule[i] != 0:
                f.write(f'{num_rule[i]},{total_num[i]},{float(num_rule[i]) / float(total_num[i])}\n')
    print('finished!')


