# from src.preprocessing_terminology import initializing
# %%
from halp.directed_hypergraph import DirectedHypergraph
from pakages.resolution.tools import renew
from src.ontology import Ontology
from src.tools import split_two_part, unfold, mkdir, trans_back, trans
from tqdm import tqdm
import re
from src.trace_inference import trace_inference
import random
from itertools import product
import line_profiler
import pickle
from queue import Queue

from src.direct_hypergraph import Direct_hyper_graph
from src.direct_graph import Direct_graph
from src.hypergraph_ont import Hypergraph_ont

import copy
import time
import os
from func_timeout import FunctionTimedOut, func_set_timeout
from src.greedy_OneModule import greedy_search


def rewrite(C):
    # transe concept (and A .... (some r  ...)...) to (and <A> .... (some <r>  ...)...)
    if " " in C:
        C_1 = C.replace(' ', '> <').replace(")", ">)")
        C_2 = C_1.replace("some >", "some ").replace("and >", 'and ').replace(")>", ')')
        return C_2.replace('<owl:Thing>', 'owl:Thing')
    else:  # C is a single atomic concept
        return f'<{C}>'


def transfer_t2C(d, n, history=set(), r_restrict=None):
    if n not in d:
        return {f'<{n}>'}
    elif n in history:
        return False
    else:
        C = ''
        atomic_conjunct = []
        history.add(n)
        for k in d[n]:
            atomic_conjunct_k = set()
            if not r_restrict or k == r_restrict:
                for n_next in d[k]:
                    result_k = transfer_t2C(d, n_next, history)
                    if result_k:
                        atomic_conjunct_k.update(result_k)
                    else:
                        return False

                if k == "":
                    atomic_conjunct += list(atomic_conjunct_k)
                else:
                    atomic_conjunct.append(f" <{'> <'.join(sorted(list(atomic_conjunct_k)))}>")

        C += f" <{'> <'.join(sorted(atomic_conjunct))}>"

        if len(atomic_conjunct) == 1:
            return C[1:]
        else:
            return f'(and{C})'


class dominant_ini(trace_inference):
    def __init__(self, name_ontology, path, sig_path='sig', count_c=None, k_E_role=None):
        trace_inference.__init__(self, path, name_ontology, count_c, k_E_role)

        # basic value
        self.name_ontology = name_ontology
        self.path = path
        self.ontology = None
        self.current_file = None
        self.sig_path = path + sig_path
        self.query_path = path + "query_" + sig_path
        mkdir(self.query_path)

        self.time_limit = 120

        self.concept_appear_count = {}

        # classification result
        self.subsumptions_direct = {}
        self.subsumptions = {}

        # hyper-graph and digraphj
        self.G = Direct_graph()
        self.G_loop_nodes = set([])
        self.H = Direct_hyper_graph()
        self.ont_H = Hypergraph_ont()

        # signature
        self.sig_r = None
        self.sig_c = None

        self.subH_id = {}

        self.nonempty_queries = []

        self.owl2ind, self.a_ind = {}, 3
        self.valid_ht = set()

        self.clauses = {'1': set()}  # assume 'final_goal' has index '1', loops part has index '2'
        self.answer_literals = set()

        self.s_t = None
        self.time_out_flag = False
        self.middle_nodes = set()

    def clear(self):
        self.clear_trace_data()
        self.H.clear()
        self.G.clear()
        self.G_loop_nodes = set([])
        self.ont_H.avaliable_edges = set([])

        self.subH_id = {}

        self.nonempty_queries = []

        self.owl2ind, self.a_ind = {}, 3
        self.valid_ht = set()

        self.clauses = {'1': set()}  # assume 'final_goal' has index '1', loops part has index '2'
        self.answer_literals = set()

        self.s_t = None
        self.time_out_flag = False
        self.middle_nodes = set()

    def initialize(self, start=True):
        self.ontology = Ontology(self.name_ontology + '.owl', self.path, True, ind_form=False)
        self.initialize_indexed_and_hyper_edges()
        self.initialize_direct_subsumption(start)
        print("initial hyper-graph and digraph loaded!")

        for n in self.ontology.concepts:
            if not self.ont_H.has_node(n):
                print('not, ', n)

        for n in self.ontology.relations:
            if not self.ont_H.has_node(n):
                print('not(r), ', n)

        self.H.concept_non_terminology = {n for n in self.concept_appear_count if self.concept_appear_count[n] > 1}
        print("non terminology concept:", len(self.H.concept_non_terminology))

    def generate_signature(self, type='', num_concept=100, num_role=10):
        concept_list_test = [num_concept] * 1000
        relation_list_test = [num_role]
        path_signature = self.path + f"sig{type}"
        path_signature_minimal_moduel = self.path + f"sig{type}_min"
        path_signature_single_minimal_moduel = self.path + f"sig{type}_single_min"
        mkdir(path_signature)
        mkdir(path_signature_minimal_moduel)
        mkdir(path_signature_single_minimal_moduel)

        i = 0
        print(len(self.ontology.concepts), len(self.ontology.relations))

        concept_list = [c for c in self.ontology.concepts if c[:3] != 'owl']
        relation_list = [r for r in self.ontology.relations if r[:3] != 'owl']

        for (li, lj) in product(relation_list_test, concept_list_test):
            sig_r = random.sample(relation_list, li)
            sig_c = random.sample(concept_list, lj)
            with open(path_signature + "/" + str(i), 'w') as fi:
                fi.write(" ".join(sig_c) + '\n')
                fi.write(" ".join(sig_r) + '\n')

            with open(path_signature_minimal_moduel + "/" + str(i), 'w') as f1:
                f1.write("concepts[\n")
                for c in sig_c:
                    f1.write("<" + c + '>\n')
                f1.write(']\nroles[\n')
                for r in sig_r:
                    f1.write("<" + r + '>\n')
                f1.write(']')

            with open(path_signature_single_minimal_moduel + "/" + str(i), 'w') as f1:
                f1.write("concepts[\n")
                for c in sig_c:
                    f1.write(c + '\n')
                f1.write(']\nroles[\n')
                for r in sig_r:
                    f1.write(r + '\n')
                f1.write(']')
            i += 1

    def renew_concept_count(self, concept_left):
        # count how many times a concept appear on left hand side of an axioms
        assert concept_left
        if concept_left in self.concept_appear_count:
            self.concept_appear_count[concept_left] += 1
        else:
            self.concept_appear_count[concept_left] = 1
        return

    def initialize_indexed_and_hyper_edges(self):
        for axiom, ind_a in self.ontology.axioms.items():
            axiom_s = axiom.split('(')
            if len(axiom_s) <= 2:
                l_1 = axiom_s[1].split('<')
                A, B = l_1[1].split('>')[0], l_1[2].split('>')[0]
                self.ont_H.add_hyperedge({A}, {B})
                self.renew_concept_count(A)
                if axiom[1] == 'e':
                    self.ont_H.add_hyperedge({B}, {A})
                    self.renew_concept_count(B)
                continue

            literal = axiom_s[2]
            type_normal, first, rest = split_two_part(axiom, type='unsort')
            concept_left = ''
            if literal[0] == 's':  # (... (some...)...)
                if type_normal:  # (implies... (some ...))
                    self.G.add_edge({first[0]}, {rest[1]},
                                    {rest[0]: ind_a})  # with attribution r: roles, i: index of axiom
                    concept_left = first[0]

                    id_G = self.G.get_hyperedge_id({first[0]}, {rest[1]})
                    self.ont_H.add_hyperedge(first, rest, {'l': id_G})
                else:  # (impies (some...) ...)
                    self.H.add_edge({first[1]}, {rest[0]}, {first[0]: ind_a})
                    concept_left = rest[0]

                    id_H = self.H.get_hyperedge_id({first[1]}, {rest[0]})
                    self.ont_H.add_hyperedge(first, rest, {'r': id_H})

                if axiom[1] == 'e':
                    if type_normal:  # (equivalence ... (some...)) --> (implies (some...) ... )
                        assert len(rest) == 2
                        self.G.add_edge({first[0]}, {rest[1]}, {rest[0]: ind_a})
                        id_G = self.G.get_hyperedge_id({first[0]}, {rest[1]})
                        self.ont_H.add_hyperedge(first, rest, {'l': id_G})

                        self.H.add_edge({rest[1]}, {first[0]}, {rest[0]: ind_a})
                        id_H = self.H.get_hyperedge_id({rest[1]}, {first[0]})
                        self.ont_H.add_hyperedge(rest, first, {'r': id_H})
                    else:  # (equivalent (some...) ...) --> (implies ... (some...))
                        assert len(first) == 2
                        self.G.add_edge({rest[0]}, {first[1]}, {first[0]: ind_a})
                        id_G = self.G.get_hyperedge_id({rest[0]}, {first[1]})
                        self.ont_H.add_hyperedge(rest, first, {'l': id_G})

                        self.H.add_edge({first[1]}, {rest[0]}, {first[0]: ind_a})
                        id_H = self.H.get_hyperedge_id({first[1]}, {rest[0]})
                        self.ont_H.add_hyperedge(first, rest, {'r': id_H})

            elif literal[:3] == 'and':  # (... (and...)...)
                if axiom[1] == 'e':
                    if type_normal:  # (equivalence ... (and...))
                        self.H.add_edge(set(rest), {first[0]}, {"h": ind_a})
                        concept_left = first[0]
                        id_H = self.H.get_hyperedge_id(set(rest), {first[0]})
                        self.ont_H.add_hyperedge(rest, first, {'r': id_H})
                        self.ont_H.add_hyperedge(first, rest)

                    else:  # (equivalence (and...) ...)
                        self.H.add_edge(set(first), {rest[0]}, {"h": ind_a})
                        concept_left = rest[0]
                        id_H = self.H.get_hyperedge_id(set(first), {rest[0]})
                        self.ont_H.add_hyperedge(first, rest, {'r': id_H})
                        self.ont_H.add_hyperedge(rest, first)

                else:
                    assert axiom[1] == 'i'
                    if not type_normal:  # (implies (and...) ...)
                        self.H.add_edge(set(first), {rest[0]}, {"h": ind_a})
                        concept_left = rest[0]
                        id_H = self.H.get_hyperedge_id(set(first), {rest[0]})
                        self.ont_H.add_hyperedge(first, rest, {'r': id_H})
                    else:
                        concept_left = first[0]
                        self.ont_H.add_hyperedge(first, rest)

            self.renew_concept_count(concept_left)

    def load_signature(self, file, type=''):
        if not type:
            path = self.sig_path + "/" + file
        else:
            path = f'{self.sig_path}_{type}/{file}'
        with open(path, 'r') as f:
            data = f.readlines()
            self.sig_c = frozenset(data[0][:-1].split(' '))
            self.sig_r = frozenset(data[1][:-1].split(' '))
            print(f'#########signature loaded!, num_concept:{len(self.sig_c)}, num_role:{len(self.sig_r)}')

        self.H.sig_c = self.sig_c
        self.H.sig_r = self.sig_r

        self.G.sig_c = self.sig_c
        self.G.sig_r = self.sig_r

    def initialize_direct_subsumption(self, start=True):
        s_t = time.time()

        if start:
            path = self.path + 'data_preprocess/subsumption_direct_terminology.owl'
            print("=======calculate direct subsumption of terminology====")
            # os.system(f'java -jar pakages/elk-tools/elk-standalone.jar -i pakages/elk-tools/{self.name_ontology}_terminology.owl -c -o {path}')

            with open(path, 'r') as f:
                data = f.readlines()
                for row in data:
                    if row[0] == 'S':
                        row_s = row.split('<')
                        assert len(row_s) == 3
                        f_id, l_id = row_s[1].split('>')[0], row_s[2].split('>')[0]
                        if f_id in self.subsumptions_direct:
                            self.subsumptions_direct[f_id].add(l_id)
                        else:
                            self.subsumptions_direct[f_id] = {l_id}

            self.subsumptions = unfold(self.subsumptions_direct)
            with open(self.path + 'data_preprocess/subsumption_terminology.owl', 'wb') as f:
                pickle.dump(self.subsumptions, f)
        else:
            with open(self.path + 'data_preprocess/subsumption_terminology.owl', 'rb') as f:
                self.subsumptions = pickle.load(f)

        self.H.subsumptions = self.subsumptions
        self.G.subsumptions = self.subsumptions
        print(time.time() - s_t)

    def extract_sub_graphs(self):
        self.G.clear()
        self.H.clear()

        _, Pe_H = self.H.traverse_forward(self.sig_c)
        # valid_edges_H = self.H.filter_hyper_edges(Pe_H)
        valid_edges_H = Pe_H
        print(len(Pe_H), len(valid_edges_H))
        print("nn:", len(self.H.nn))
        if len(valid_edges_H) < 0:
            s_t_local = time.time()
            H_ids, G_ids = self.ont_H.traverse(self.sig_c | self.sig_r)
            print("*****local module", len(H_ids), len(G_ids))
            print("*****time local:", time.time() - s_t_local)
            valid_edges_H &= H_ids

        valid_nodes = self.G.traverse_forward(self.H.node_start | self.sig_c)
        print(len(self.G.subgraph_sig.get_hyperedge_id_set()))

        for n in valid_nodes & self.H.node_start:
            if n in self.concept_appear_count and self.concept_appear_count[n] > 1 and n not in self.sig_c:
                self.middle_nodes.add(n)

        print("middle_nodes:", len(self.middle_nodes), len(self.middle_nodes & self.sig_c))
        print("H start, G start:", len(self.H.node_start), len(self.G.node_start))
        self.H.traverse_backward(self.middle_nodes | self.sig_c, valid_edges_H)
        # self.H.traverse_backward(self.sig_c, valid_edges_H)
        print("after(H):", len(self.H.subgraph_sig.get_hyperedge_id_set()))

    def filter_redundancy_and_equivalence(self):
        owl_str = ''
        self.owl2ind, self.a_ind = {}, 3  # assume 'final_goal' has index '1', loops part has index '2'
        # A\sqsubseteq B
        initilal_subsumption = {}
        for n in self.sig_c:
            if n in self.subsumptions:
                for n_super in self.subsumptions[n] & self.sig_c:
                    owl_str += trans_back(f'(implies <{n}> <{n_super}>)\n')
                    self.owl2ind[f'{n} {n_super}'] = str(self.a_ind)
                    initilal_subsumption[str(self.a_ind)] = (n, n_super)
                    self.a_ind += 1

        # C \sqsubseteq B, B in signature
        m2C = {}
        C_defined = {}
        ind2CD = {}
        for s_h_id in self.subH_id:
            head, C = self.subH_id[s_h_id]
            assert C[0] == '('
            if C not in C_defined and C[0] == '(':
                owl_str += trans_back(f'(equivalent <N_{s_h_id}> {C})\n')
                C_defined[C] = f'N_{s_h_id}'

            if head in self.sig_c:
                owl_str += trans_back(f'(implies <{C_defined[C]}> <{head}>)\n')
                self.owl2ind[f'{C_defined[C]} {head}'] = str(self.a_ind)
                ind2CD[str(self.a_ind)] = (head, s_h_id, None)
                self.a_ind += 1
            else:
                print("not in signature!", C, head)
                assert head in self.middle_nodes
                if head in m2C:
                    m2C[head].add(C_defined[C])
                else:
                    m2C[head] = {C_defined[C]}

        # A \sqsubseteq C, A in signature
        D_defined = {}
        print(self.G.cluster.A2L)
        for n in self.middle_nodes | self.sig_c:
            if n in self.G.cluster.A2L:
                dic = self.G.cluster.A2L[n]
                for r in dic:
                    if r != '':  # here we ignore cases A\sqsubseteq B
                        for n_next in dic[r]:
                            for D in self.G.cluster.transfer2C(n, r_res=r, k_res=n_next):
                                if len(re.split('<|:', D)) <= 2:
                                    continue
                                if D not in D_defined:
                                    if isinstance(n_next, str):
                                        n_next_str = n_next
                                    else:
                                        n_next_str = "-".join(n_next)
                                    owl_str += trans_back(f'(equivalent <M{n}_{r}_{n_next_str}> {D})\n')
                                    D_defined[D] = f'M{n}_{r}_{n_next_str}'

                                if n in self.sig_c:
                                    owl_str += trans_back(f'(implies <{n}> <{D_defined[D]}>)\n')
                                    self.owl2ind[f'{n} {D_defined[D]}'] = str(self.a_ind)
                                    ind2CD[str(self.a_ind)] = (n, None, (r, n_next))
                                    self.a_ind += 1
                                else:
                                    # assert n in m2C
                                    if n in m2C:
                                        for N_C in m2C[n]:
                                            owl_str += trans_back(f'(implies <{N_C}> <{D_defined[D]}>)\n')
                                            self.owl2ind[f'{N_C} {D_defined[D]}'] = str(self.a_ind)
                                            ind2CD[str(self.a_ind)] = (n, N_C, (r, n_next))
                                            self.a_ind += 1

        path_owl = self.path + 'filter_redundancy.owl'
        with open(path_owl, 'w') as f:
            f.write(f"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n{owl_str})\n")
            # f.write("Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n{}\n)\n".format('\n'.join(self.owl2ind.keys())))

        path_sub = self.path + 'filter_subsumption.txt'
        with open(path_sub, 'w') as f:
            f.write('\n'.join(self.owl2ind.keys()) + '\n')

        # compute dominance
        path_result = self.path + 'filter_result.txt'
        command = f"java -jar pakages/numjust/numOfJust.jar {path_owl} {path_sub} {path_result} | grep '^[0-9]*$' | tail -n 1"
        os.system(command)
        # onto = ol.get_ontology(path_owl).load()
        # print(list(onto.classes()))

        # load dominance
        dic_dominant = DirectedHypergraph()
        dic_dominant.add_nodes(self.owl2ind.values())
        redundant_ind = set()
        # filter equivalent nodes
        node_direct_subsumption = {}
        with open(path_result, 'r') as f:
            for line in f.readlines():
                li = re.sub("SubClassOf|\(|\)|<|>", "", line).split(',')[:-1]
                head = [self.owl2ind[li[0]]]
                for p in li[1:]:
                    tail = {self.owl2ind[a] for a in p.split("\t")[:-1] if a[0] != 'E'}

                    if not tail:
                        redundant_ind.add(head[0])
                        print(li[0], p)
                        break
                    elif head[0] in tail:
                        continue

                    if len(tail) == 1:
                        for t in tail:
                            if t in node_direct_subsumption:
                                node_direct_subsumption[t].add(head[0])
                            else:
                                node_direct_subsumption[t] = {head[0]}

                    dic_dominant.add_hyperedge(tail, head)
                pass

        # first, find equivalent nodes
        print(node_direct_subsumption)
        node_direct_subsumption = unfold(node_direct_subsumption)
        print(node_direct_subsumption)
        print(redundant_ind)
        all_nodes = dic_dominant.get_node_set()
        # delete all k such that k in node_direct_subsumption[k1] and k1 not in node_direct_subsumption[k]
        for n in all_nodes:
            if n not in node_direct_subsumption:
                n_dominate_set = set()
            else:
                n_dominate_set = node_direct_subsumption[n]

            for k in node_direct_subsumption:
                if n in node_direct_subsumption[k] and k not in n_dominate_set:
                    dic_dominant.remove_node(n)
                    redundant_ind.add(n)
                    break
        print(redundant_ind)

        # we delete all node that has only income edges
        while True:
            f = False
            all_nodes = list(dic_dominant.node_iterator())
            for n in all_nodes:
                if not dic_dominant.get_forward_star(n) and dic_dominant.get_backward_star(n):
                    dic_dominant.remove_node(n)
                    redundant_ind.add(n)
                    f = True
            if not f:
                break

        print(redundant_ind)

        # !!! make sure the index is unified
        self.count_id = self.a_ind

        # encode the derivation relations among all C->D
        for h_id in dic_dominant.get_hyperedge_id_set():
            tail = dic_dominant.get_hyperedge_tail(h_id)
            head_set = dic_dominant.get_hyperedge_head(h_id)
            print(h_id, head_set, tail)
            assert len(head_set) == 1
            for head in head_set:
                if head in self.clauses:
                    self.clauses[head].append(tail)
                else:
                    self.clauses[head] = [tail]

        # print(self.clauses)

        # add clause for C->A + A->D => C->D
        for node in dic_dominant.get_node_set():
            if node in initilal_subsumption:
                A, B = initilal_subsumption[node]
                id_subsumption = self.setid_rules2id(
                    str(self.concepts2id[A]) + "\t" + str(self.concepts2id[B]))

                if node in self.clauses:
                    print(node, self.clauses[node])
                    print(f'edge {node} corresponding to subsumption {A}->{B} is already in the clauses !')
                self.clauses[node] = {id_subsumption}

            if node in ind2CD:
                A, e_id, D_tuple = ind2CD[node]
                pre_ids = []
                if e_id:
                    pre_ids.append(self.setid_rules2id(e_id))
                    self.valid_ht.add(e_id)
                if D_tuple:
                    pre_ids.append(self.setid_rules2id((A, D_tuple)))
                    self.valid_ht.add((A, D_tuple))

                self.clauses[node] = [pre_ids]

        # '0' is the index of 'final_goal'
        self.clauses['1'].update(dic_dominant.node_iterator())

        print("filter redundancy: ", self.clauses)
        print(self.owl2ind)
        print(ind2CD)
        print(self.rules2id)
        return

    def build_cnf_t_one(self, A, id_A, id_history=set([])):
        subsumption_paris = set([])

        dic = self.G.cluster.A2L[A]
        for r in dic:
            if r == '':
                for A_sig in dic[r]:
                    if isinstance(A_sig, tuple):
                        id_A_sig_tuple = self.setid_rules2id(A_sig)
                        renew(self.clauses, id_A, id_A_sig_tuple)
                        for A_i in A_sig:
                            assert A_i in self.sig_c
                            subsumption_paris.add((A, A_i))
                            id_subsumption = self.setid_rules2id(
                                str(self.concepts2id[A]) + "\t" + str(self.concepts2id[A_i]))
                            renew(self.clauses, id_A_sig_tuple, id_subsumption)
                    else:
                        assert A_sig in self.sig_c
                        subsumption_paris.add((A, A_sig))
                        id_subsumption = self.setid_rules2id(
                            str(self.concepts2id[A]) + "\t" + str(self.concepts2id[A_sig]))
                        renew(self.clauses, id_A, id_subsumption)

                continue

            for B in dic[r]:
                # avoid redundant cluster
                if A in self.sig_c | self.middle_nodes and (A, (r, B)) not in self.valid_ht:
                    continue

                id_tuple = self.setid_rules2id((A, (r, B)))

                # only include the clause id_tuple+...-> id_A when A in sig_C or middle nodes
                if A not in self.sig_c | self.middle_nodes:
                    renew(self.clauses, id_A, id_tuple)

                if not isinstance(B, tuple):
                    B_tuple = tuple([B])
                else:
                    B_tuple = B

                for b in B_tuple:
                    set_pre_B = set()
                    g_id = self.G.subgraph_sig.get_hyperedge_id({A}, {b})
                    for original_g_id in self.G.subgraph_sig_h_id2r_and_H_id[g_id][r]:
                        axiom_id = self.G.get_hyperedge_attribute(original_g_id, r)
                        axiom_id_in_clause = self.setid_rules2id(axiom_id)
                        self.answer_literals.add(axiom_id_in_clause)
                        set_pre_B.add(axiom_id_in_clause)

                        orginal_tails = self.G.get_hyperedge_tail(original_g_id)
                        assert len(orginal_tails) == 1
                        for tail in orginal_tails:
                            if A != tail:
                                subsumption_paris.add((A, tail))
                                id_subsumption = self.setid_rules2id(
                                    str(self.concepts2id[A]) + "\t" + str(self.concepts2id[tail]))
                                set_pre_B.add(id_subsumption)

                    if b in self.G.cluster.A2L and b not in self.sig_c | self.middle_nodes:
                        if ('l', b) in self.rules2id:
                            f_appeared = True
                        else:
                            f_appeared = False

                        id_b = self.setid_rules2id(("l", b))
                        if id_b in id_history:
                            # loop
                            self.G_loop_nodes.add(b)
                        else:
                            set_pre_B.add(id_b)
                            if not f_appeared:
                                subsumption_paris.update(self.build_cnf_t_one(b, id_b, id_history | {id_b}))

                    renew(self.clauses, id_tuple, set_pre_B, type='append')
        return subsumption_paris

    def build_cnf_t(self):
        subsumption_paris = set()
        # trace cluster
        for A in self.sig_c | self.middle_nodes:
            if A in self.G.cluster.A2L:
                id_A = self.setid_rules2id(("l", A))
                subsumption_paris.update(self.build_cnf_t_one(A, id_A))

        print('clause for clusters traced!!')
        print('num clauses: ', len(self.clauses))
        print(len(self.rules2id), len(subsumption_paris))
        return subsumption_paris

    def build_cnf_h(self):
        # loop part of clusters have already included !!! since we do not compare two loops when cut redundancy.
        subsumption_pairs = set([])

        Q = Queue()
        pre_loop_ids = set()
        for e_id in self.H.subgraph_sig.loop_h_id:
            Q.put(e_id)
            pre_loop_ids.add(self.setid_rules2id(e_id))

            assert e_id not in self.H.subgraph_sig.id2subsumptions

        for e_id in self.subH_id:
            Q.put(e_id)

        if pre_loop_ids:
            self.clauses['2'] = [pre_loop_ids]
            self.clauses['1'].add('2')

        # traverse all hyperedge and r-edge
        while not Q.empty():
            current_e_id = Q.get()
            current_e_new_id = self.setid_rules2id(current_e_id)

            if current_e_id in self.H.subgraph_sig.subH_id_inferences:
                for edges in self.H.subgraph_sig.subH_id_inferences[current_e_id]:
                    edges_id = set()
                    for e in edges:
                        if e in self.H.subgraph_sig.id2subsumptions:
                            # e represent a subsumption derived by ontology
                            subsumptions = self.H.subgraph_sig.id2subsumptions[e]
                            subsumption_pairs.add(tuple(subsumptions))
                            edges_id.add(self.setid_rules2id(
                                str(self.concepts2id[subsumptions[0]]) + "\t" + str(self.concepts2id[subsumptions[1]])))
                        else:
                            edges_id.add(self.setid_rules2id(e))

                            if e in self.H.subgraph_sig.subH_id_inferences:
                                Q.put(e)
                            # else, e is an axiom id of orginal ontology

                    # add new clause edges_id--> current_e_new_id
                    renew(self.clauses, current_e_new_id, edges_id, type='append')

        print('clause for hyper-paths traced!!')
        print('num of clauses: ', len(self.clauses))
        print(len(self.rules2id), len(subsumption_pairs))
        return subsumption_pairs

    def build_cnf(self, k, ):
        subsumption_paris = self.build_cnf_t()
        subsumption_paris.update(self.build_cnf_h())
        print('num of subsumption pairs: ', len(subsumption_paris))

        # trace cnf formula for subsumptions
        result, s_a_pre, goal_id = self.trace_inference_rules(subsumption_paris)
        self.clauses.update(result)

        s_a = {str(a) for a in s_a_pre}
        self.answer_literals.update(s_a)
        # add axiom id generated when extracting hyper-paths
        for a_id in self.H.axioms_id & self.rules2id.keys():
            a_clause_id = self.setid_rules2id(a_id)
            self.answer_literals.add(a_clause_id)
        print('num of answer literals', len(self.answer_literals))

        # check if the cnf-formula is correct
        self.check_dic = {}
        self.check_history = []
        self.flag_loop = False
        self.check(self.clauses, self.answer_literals, '1')

        # write cnf formula in file
        self.write_cnf(k)

        return

    def check(self, result, s_a, k):
        if k in self.check_history:
            self.flag_loop = True
            return False

        if self.flag_loop:
            return False

        if k in self.check_dic:
            return self.check_dic[k]
        elif k not in result:
            if k not in s_a and str(k) not in s_a and int(k) not in s_a:
                print("not:", k)
                return False
            else:
                return True

        self.check_history.append(k)
        if isinstance(result[k], set):
            for e in result[k]:
                if e in s_a:
                    continue
                if not self.check(result, s_a, e):
                    print("false:", e)
                    assert self.check_history[-1] == k
                    self.check_history.pop()
                    return False
        else:
            for l in result[k]:
                for e in l:
                    if e in s_a:
                        continue
                    if not self.check(result, s_a, e):
                        print("false:", e)
                        assert self.check_history[-1] == k
                        self.check_history.pop()
                        return False

        self.check_dic[k] = True
        assert self.check_history[-1] == k
        self.check_history.pop()
        return True

    def write_cnf(self, k):
        query_file = f'{self.query_path}/{k}'
        self.nonempty_queries.append(str(k))
        mkdir(query_file)

        with open(f"{query_file}/encoding.cnf", 'w') as f_a:
            for k in self.clauses:
                if not self.clauses[k]:
                    f_a.write(f'{k} 0\n')
                elif isinstance(self.clauses[k], set):
                    f_a.write('-' + ' -'.join(list(self.clauses[k])))
                    f_a.write(f' {k} 0\n')
                else:
                    assert isinstance(self.clauses[k], list)
                    premise_set_filtered = set([frozenset(s) for s in self.clauses[k]])
                    for l_k in premise_set_filtered:
                        f_a.write('-' + ' -'.join(list(l_k)))
                        f_a.write(f' {k} 0\n')

        with open(f"{query_file}/encoding.assumptions", 'w') as f_c:
            l_s_a = [str(b) for b in self.answer_literals]
            f_c.write(' '.join(l_s_a) + ' 0\n')

        with open(f"{query_file}/encoding.q", 'w') as f_q:
            f_q.write(str('1') + '\n')

        print("______________Complete Module_____________")
        with open(f'{query_file}/approximate_module.owl', 'w') as f_o:
            # f_o.write(f"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n")
            for axiom in self.ontology.axioms:
                ind_a = self.ontology.axioms[axiom]
                if ind_a in self.rules2id and str(self.rules2id[ind_a]) in self.answer_literals:
                    line = str(self.rules2id[ind_a]) + ": "+ trans_back(axiom) 
                    f_o.write(line+ "\n")
                    print(line)
            # f_o.write(')\n')
        print("___________________________________________")

    def record_subH(self):
        # extract hyper-paths to a node in sig_c or a middle node
        valid_nodes = self.sig_c | self.middle_nodes
        nodes_left = set()
        for h_id in self.H.subgraph_sig.hyperedge_id_iterator():
            print(self.H.subgraph_sig.get_hyperedge_attributes(h_id))
            head = self.H.subgraph_sig.get_hyperedge_head(h_id)
            tail = self.H.subgraph_sig.get_hyperedge_tail(h_id)

            assert tail.issubset(valid_nodes)

            li = [None, None]  # [node, C]
            for n in head:
                if n in valid_nodes:
                    assert n[0] != "(" and n[0] != '<'
                    li[0] = n

                if n[0] == '(' or n[0] == '<':
                    assert n not in valid_nodes
                    li[1] = n

            assert li[0] and li[1]
            if li[1][0] == "(":
                nodes_left.add(li[1])
                self.subH_id[h_id] = tuple(li)

        self.middle_nodes = nodes_left
        return

    @func_set_timeout(60)
    def main(self, k, type=''):
        self.clear()

        self.load_signature(k, type)
        s_t = time.time()

        # extract cluster
        self.extract_sub_graphs()
        print("time extract sub hyper-graph:", time.time() - s_t)

        # extract hyper-paths
        self.H.enumerate_hyper_paths(self.sig_c | self.middle_nodes)
        self.H.enumerate_hyper_paths(self.sig_c, False)
        self.record_subH()

        # extract cluster
        self.G.build_cluster(self.sig_c | self.middle_nodes)
        print('size clauses:', len(self.G.cluster.A2L))
        print("time extract hyper-path and cluster:", time.time() - s_t)
        time_clusterandhyper_path = time.time() - s_t

        # delete redundant part
        s_t_1 = time.time()
        self.filter_redundancy_and_equivalence()
        print("time filter redundancy:", time.time() - s_t)

        self.build_cnf(k)
        time_cnf = time.time() - s_t_1
        print("time all:", time.time() - s_t)

        print("clauses, answer_literals: ", len(self.clauses), len(self.answer_literals))
        return time_clusterandhyper_path, time_cnf


def test(path, name_ontology, count_c=None, k_E_role=None, type=''):
    m = dominant_ini(name_ontology, path, count_c=count_c, k_E_role=k_E_role)
    m.initialize()
    if not type:
        m.query_path = path + "query_sig"
    else:
        m.query_path = path + "query_sig_small"

    len_sig = len(os.listdir(m.sig_path))
    test_sample = range(len_sig)

    s_t = time.time()
    time_out_list = []
    f_record = open(f'{path}/record_time_sig{type}.txt', 'w')
    f_record.write(
        'k, time_of_cluster_and_hyper_path, time_of_cnf,time_greedy, answer_literals, greedy_one_module_size, contain_loop, garantee_minimal, loop_h_id, loop_pairs, G_loop_nodes\n')
    for k in test_sample:
        print('___________signature:', k)
        try:
            t_ch, t_cnf = m.main(str(k), type)
        except FunctionTimedOut:
            time_out_list.append(k)
            continue
        # contain loops
        if m.H.subgraph_sig.loop_h_id or m.G.cluster.loops_pairs or m.G_loop_nodes:
            f_loop = True
        else:
            f_loop = False

        # minimal or not
        if not m.H.subgraph_sig.loop_h_id and not m.G.cluster.loops_pairs:
            f_minimal = True
        else:
            f_minimal = False

        s_t = time.time()
        OneM = greedy_search(m.clauses, m.answer_literals)
        module1 = OneM.search('1')
        time_greedy = time.time() - s_t

        # record time and only preserve 5 digits
        f_record.write(
            f'{k}, {round(t_ch, 5)}, {round(t_cnf, 5)}, {time_greedy}, {len(m.answer_literals)}, {len(module1)}, '
            f'{f_loop}, {f_minimal}, {m.H.subgraph_sig.loop_h_id, m.G.cluster.loops_pairs}, {m.G_loop_nodes}\n')
        f_record.flush()
    print(time_out_list)
    f_record.close()

    with open(f'{path}/non_time_out_sig{type}.txt', 'w') as f_o:
        for k in test_sample:
            if k not in time_out_list:
                f_o.write(f'{k}\n')

    return time_out_list, time.time() - s_t, m


if __name__ == "__main__":
    s_t = time.time()
    from sys import argv

    path = f'workspace/{argv[1]}/'
    name_ontology = argv[1]
    count_c, k_E_role = None, None
    time_out_list, all_time, m = test(path, name_ontology, count_c, k_E_role, '')
    print('all done in', time.time() - s_t)
