import os

from pakages.resolution.tools import renew
import copy
import itertools
from src.tools import trans_back
from halp.directed_hypergraph import DirectedHypergraph
from halp.algorithms import k_shortest_hyperpaths
import networkx as nx
import matplotlib.pyplot as plt


class equi_sets:
    def __init__(self):
        self.collection = []

    def add(self, e1, e2):
        # here e1=e2
        for s in self.collection:
            if e1 in s:
                s.add(e2)
                break
            if e2 in s:
                s.add(e1)
                break
        else:
            self.collection.append({e1, e2})

    def add_unequal(self, e1, e2, type="keep_max"):
        # here e1<e2 and e1!=e2
        del_ind = []
        f_add = True
        for i, s in enumerate(self.collection):
            if type == "keep_max":
                if e1 in s:
                    del_ind.append(i)
                if e2 in s:
                    f_add = False
            else:
                if e2 in s:
                    del_ind.append(i)
                if e1 in s:
                    f_add = False

        if f_add:
            if type == "keep_max":
                self.collection.append({e2})
            else:
                self.collection.append({e1})

        self.collection = [self.collection[i] for i in range(len(self.collection)) if i not in del_ind]

    def add_equal(self, s):
        del_ind = []
        for i, s1 in enumerate(self.collection):
            if s1 & s:
                assert len(s1) == 1
                del_ind.append(i)

        self.collection = [self.collection[i] for i in range(len(self.collection)) if i not in del_ind]
        self.collection.append(s)

    def get_result(self):
        return tuple(tuple(a) for a in self.collection)


def check_repeat_loops(d, k, l, end_nodes_k):
    # k=(start_node, ind_edge)
    e_inds = []
    for li in d:
        # if d[li] == k:
        if d[li][0] in end_nodes_k:
            e_inds.append(li)

    if not e_inds:
        return False
    else:
        return True
        min_e_inds = min(e_inds)
        while min_e_inds >= 1 and l > 0:
            min_e_inds -= 1
            k_pre = d[l - 1]
            e_inds = [i - 1 for i in e_inds if d[i - 1] == k_pre]
            if not e_inds:
                return False
            elif e_inds and k_pre[0] in end_nodes_k:
                return True
            l -= 1

    return False


def tensor_prod(l1, l2):
    if not l1:
        return l2
    if not l2:
        return l1
    result = set()
    for a1 in l1:
        for a2 in l2:
            # print(a1, a2)
            new_item = set(a1)
            new_item.update(a2)
            result.add(tuple(sorted(list(new_item))))

    return result


def check_loops(d, l, end_nodes_k):
    # k=(start_node, ind_edge)
    for li in range(l - 1, -1, -1):
        if d[li][0] in end_nodes_k:
            assert [d[j] for j in range(li, l)]
            return [d[j] for j in range(li, l)]
    return []


class superdic:
    def __init__(self, sig_c=set([]), d_C=set([])):
        # {  A: [ {"": [B_i,....],..., r: [A_j ,...],...}, 
        #          ... 
        #        ]  } 
        self.A2L = {}

        self.H = DirectedHypergraph()
        self.G = nx.DiGraph()

        self.paths = []
        self.simple_loops = {}

        self.A_order = {}
        self.order = 0
        self.sig_c = sig_c
        self.definite_C = d_C

        self.super_history = []
        self.loops = False

        self.r_paths = []
        self.node_history = []
        self.role_history = []
        self.nontrivial_loops = False

        self.A2Super = {}
        self.A2NoSuper = {}

    def add(self, A, li, F_A):
        assert A not in self.A2L
        assert isinstance(li, list)

        self.A2L[A] = li

        self.A_order[A] = self.order
        self.order += 1

        for B in F_A:
            self.A_order[B] = self.order
            self.order += 1

    def filter(self):
        A_Order = sorted(self.A_order.items(), key=lambda x: x[1])

        L_A = [x[0] for x in A_Order]
        L_A.reverse()

        Empty_A = {A for A in self.A2L if self.A2L[A] == [{}]}
        for A in Empty_A:
            del self.A2L[A]

        del_A = set([])
        for A in L_A:
            # filter redundant A in self.A2L
            if A not in self.A2L:
                # assert A not in self.sig_c
                if A not in self.sig_c:
                    del_A.add(A)
                continue

            li = self.A2L[A]
            preserve_ind = set([])
            for i in range(len(li)):
                dic = li[i]
                if "" not in dic:
                    redundant_r = []
                    for r in dic:
                        dic[r] -= del_A
                        if not dic[r]:
                            redundant_r.append(r)
                        else:
                            preserve_ind.add(i)

                    for r in redundant_r:
                        del dic[r]
                else:
                    preserve_ind.add(i)

            if not preserve_ind:
                del self.A2L[A]
                if A not in self.sig_c:
                    del_A.add(A)
            else:
                self.A2L[A] = [li[i] for i in preserve_ind]

        for A in del_A:
            del self.A_order[A]
            if A in self.A2L:
                del self.A2L[A]

        return

    def filter_right(self):
        # self.filter_dics()  # remove redundant dics
        Empty_A = {A for A in self.A2L if self.A2L[A] == [{}]}

        for A in Empty_A:
            del self.A2L[A]

        A_Order = sorted(self.A_order.items(), key=lambda x: x[1])

        L_A = [x[0] for x in A_Order]
        L_A.reverse()

        del_A = set([])
        for A in L_A:
            # filter redundant A in self.A2L
            if A not in self.A2L:
                if A not in self.sig_c:
                    del_A.add(A)
                continue

            li = self.A2L[A]
            len_li = len(li)
            del_i = set([])
            for i in range(len_li):
                dic = li[i]
                for r in dic:
                    if dic[r] & del_A:
                        del_i.add(i)

            if len(del_i) == len_li:
                del self.A2L[A]
                if A not in self.sig_c:
                    del_A.add(A)
            else:
                self.A2L[A] = [li[i] for i in range(len_li) if i not in del_i]

        for A in del_A:
            del self.A_order[A]

        self.filter_dics()
        return

    def filter_redundant_key(self):
        valid_keys = copy.deepcopy(self.sig_c)
        for A in self.A2L:
            for dicOrlist in self.A2L[A]:
                dic_lists = []
                if isinstance(dicOrlist, list):
                    dic_lists += dicOrlist
                else:
                    dic_lists.append(dicOrlist)

                for one_dict in dic_lists:
                    for r in one_dict:
                        for term in one_dict[r]:
                            if isinstance(term, tuple):
                                for t in term:
                                    valid_keys.update(t)
                            else:
                                valid_keys.add(term)

        redundant_keys = []
        for A in self.A2L:
            if A not in valid_keys:
                redundant_keys.append(A)

        for A in redundant_keys:
            del self.A2L[A]

    def filter_ConceptInSameRole(self, type='keep_max'):
        A2L_new = {}
        for A in self.A2L:
            A2L_new[A] = []
            li = self.A2L[A]
            new_dic = {}
            for dic in li:
                for r in dic:
                    concepts_correspond2r = dic[r]
                    if len(concepts_correspond2r) == 1:
                        new_dic[r] = concepts_correspond2r
                        continue
                    equal_c = equi_sets()
                    redundant_c = set([])
                    smaller_c = set([])
                    for c1, c2 in itertools.combinations(concepts_correspond2r, 2):
                        if type == "keep_max":
                            f = False
                            if self.super(c1, c2):
                                redundant_c.add(c1)
                                f = True

                            if self.super(c2, c1):
                                redundant_c.add(c2)
                                if f:
                                    equal_c.add(c1, c2)
                        else:
                            f = False
                            self.super_history = []
                            if self.super(c1, c2):
                                redundant_c.add(c2)
                                f = True

                            self.super_history = []
                            if self.super(c2, c1):
                                redundant_c.add(c1)
                                if f:
                                    equal_c.add(c1, c2)
                                else:
                                    smaller_c.add(c1)
                            else:
                                if f:
                                    smaller_c.add(c2)

                    filter_conceptes = {A for A in dic[r] if A not in redundant_c}
                    equal_c_tuples = equal_c.get_result()
                    equal_c_filtered = []

                    for t in equal_c_tuples:
                        for ti in t:
                            if ti in smaller_c:
                                break
                        else:
                            equal_c_filtered.append(t)

                    if equal_c_filtered:
                        filter_conceptes.add(tuple(equal_c_filtered))
                    new_dic[r] = filter_conceptes

            A2L_new[A].append(new_dic)

        self.A2L = A2L_new

        self.filter_redundant_key()

    def filter_dics(self):
        def compare_dic(d1, d2):
            for r in d1:
                if r not in d2:
                    return False
                elif not d1[r].issubset(d2[r]):
                    return False
            return True

        for A in self.A2L:
            li = self.A2L[A]
            redundant_ind = set([])
            for ind1, ind2 in itertools.combinations(range(len(li)), 2):
                dic1, dic2 = li[ind1], li[ind2]
                if dic1 == dic2:
                    redundant_ind.add(ind2)
                else:
                    if ind1 in redundant_ind or ind2 in redundant_ind:
                        continue

                    if compare_dic(dic1, dic2):
                        redundant_ind.add(ind2)
                    elif compare_dic(dic2, dic1):
                        redundant_ind.add(ind1)

                filter_dic = [li[i] for i in range(len(li)) if i not in redundant_ind]
                self.A2L[A] = filter_dic

    def clusters(self, n):
        # assume n not in self.sig_c
        all_clusters, ended_nodes = [], set([])
        for p in nx.all_simple_edge_paths(self.G, n, 'T'):
            # print(p)
            ended_nodes.add(p[-1][1])
            for cl in all_clusters:
                pre_ind, flag_add = '', False
                for i, e in enumerate(p):
                    new_v = (e[1], self.G[e[0]][e[1]]["r"])
                    if flag_add:
                        if e[0] in cl:
                            cl[e[0]].append(new_v)
                        else:
                            cl[e[0]] = [new_v]
                    if cl[e[0]] == [new_v]:
                        pre_ind += self.G[e[0]][e[1]]["r"]
                    else:
                        if not pre_ind:
                            break
                        else:
                            flag_add = True
                else:
                    continue
                break
            else:
                new_cl = {e[0]: [(e[1], self.G[e[0]][e[1]]["r"])] for e in p}
                all_clusters.append(new_cl)

        return all_clusters, ended_nodes

    # whether n1 is smaller than n2
    def super_path_left(self, n1, n2):
        lp1, lp2 = self.simple_loops[n1], self.simple_loops[n2]

        # compare loops
        lp1_new = list(lp1)

        def decomposeble(s, S):
            # whether s = s1+s2+..+sn for si in S
            if not s:
                return True
            for si in S:
                l_si = len(si)
                if l_si > len(s):
                    continue
                if s[:l_si] == si and decomposeble(s[l_si:], S):
                    return True
            return False

        for s1 in lp1:
            S1 = []
            for s2 in lp2:
                if s2 in s1:
                    S1.append(s2)
            if not decomposeble(s1, S1):
                return False

        # compare (acyclic) sub-graphs
        cl1, e_nd1 = self.clusters(n1)
        cl2, e_nd2 = self.clusters(n2)

        if not e_nd1.issubset(e_nd2):
            return False
        else:
            return False

    def unfold_path_A(self, A, hist={}, l=0):
        result = []
        if A in self.A2L:
            hist_new = copy.deepcopy(hist)
            for ind_dic, dic in enumerate(self.A2L[A]):
                # ignore trivial loops, case 1
                if dic.get("") and A in dic[""]:
                    continue
                # ignore trivial loops, case 2
                if l > 0:
                    if '' in dic and hist[l - 1][0] in dic['']:
                        continue
                end_nodes_i = set([])
                for r in dic:
                    end_nodes_i.update(dic[r])

                hist_new[l] = (A, ind_dic)
                assert l + 1 == len(hist_new)
                loop = check_loops(hist_new, l + 1, end_nodes_i)
                if loop:
                    continue

                pools = [set(hist_new.values())]
                for k in dic:
                    for B in dic[k]:
                        if B in sig_c:
                            continue
                        new_path_from_B = self.unfold_path_A(B, hist_new, l + 1)
                        if new_path_from_B or B in sig_c:
                            pools = tensor_prod(pools, self.unfold_path_A(B, hist_new, l + 1))
                        else:
                            break
                    else:
                        break
                else:
                    pools = []
                result += pools
        else:
            assert A in self.sig_c
        print(len(result), result[:10])
        return result

    def unfold_path(self):
        for A in self.sig_c:
            if A in self.A2L:
                print(A)
                self.paths += self.unfold_path_A(A)
                print("len self.path", len(self.paths))

    def unfold_loops(self):
        edges = []
        for A in self.A2L:
            for dic in self.A2L[A]:
                for r in dic:
                    if not dic[r]:
                        edges.append((A, "T", {'r': r}))  # include owl:Thing
                    for B in dic[r]:
                        edges.append((A, B, {'r': r}))

        self.G.add_edges_from(edges)
        print(len(edges))

        nx.draw(self.G)
        plt.show()

        for c in nx.simple_cycles(self.G):
            l_c = len(c)
            c_ind = [self.G.edges[c[i], c[i + 1]]['r'] for i in range(l_c - 1)]
            c_ind.append(self.G.edges[c[l_c - 1], c[0]]['r'])
            if set(c_ind) != {""}:
                for i, c_i in enumerate(c):
                    ind_i = ""
                    for j in range(i, i + l_c):
                        if j >= l_c:
                            j1 = j - l_c
                        else:
                            j1 = j
                        if c_ind[j1] != "":
                            ind_i += c_ind[j1] + ' '
                    if c_i in self.simple_loops:
                        self.simple_loops[c_i].add(ind_i)
                    else:
                        self.simple_loops[c_i] = {ind_i}
        for n in self.sig_c:
            if self.G.has_node(n):
                self.G.add_edge(n, 'T', r="")

        print(len(self.simple_loops))

    def extract_hyper_path(self):
        for A in self.A2L:
            for dic in self.A2L[A]:
                for r in dic:
                    self.H.add_hyperedge(dic[r], {A})

        print(self.H.is_B_hypergraph())

        nodes = [A for A in self.sig_c if self.H.has_node(A)]
        print(len(nodes), len(self.sig_c))
        for n in nodes:
            self.H.add_hyperedge({'r'}, {n})

        for n in nodes:
            paths = k_shortest_hyperpaths.k_shortest_hyperpaths(self.H, 'r', n, 10000)
            print(len(paths))
            if len(paths) == 10:
                for p in paths:
                    p.write('paths.txt')

    def clear(self):
        self.A2L = {}
        self.paths = []

        self.A_order = {}
        self.order = 0

        self.super_history = []
        self.loops = False

        self.r_paths = []
        self.node_history = []
        self.role_history = []
        self.nontrivial_loops = False

        self.A2Super = {}
        self.A2NoSuper = {}

    # keep only maximal(or min) element of A
    def main(self, type='keep_max'):
        if type == 'keep_max':
            # right dominant module
            self.unfold_hyper_path()  # enumerate all hyper-paths and delete smaller ones
            print("dics filtered!")
        else:
            # left dominant module
            self.filter_ConceptInSameRole(type)

            Empty_A = {A for A in self.A2L if self.A2L[A] == [{'': {()}}] or self.A2L[A] == [{"": set()}]}
            for A in Empty_A:
                del self.A2L[A]


if __name__ == "__main__":
    sig_c = {'24864', '124868', '80986', '35095', '57974', '74973', '34435', '07805', '75264', '96157', '53053',
             '010197', '42156', '109987', '93125', '44848', '62911', '119499', '41177', '38172', '13482', '103933',
             '93038', '88872', '36047', '15459', '25075', '56251', '50448', '116600', '53728', '62227', '108608',
             '19032', '33187', '89831', '37855', '23255', '81535', '9777', '83689', '010124', '66553', '70507', '57375',
             '5189', '15929', '476', '63122', '1542', '65912', '47734', '014888', '121031', '61463', '25465', '119035',
             '95435', '122890', '23515', '2097', '112211', '55458', '52927', '89428', '99558', '99680', '29983',
             '03752', '22037', '76879', '39651', '39926', '78163', '01620', '116558', '18987', '3884', '9032', '94672',
             '76494', '8848', '95850', '37330', '017495', '44593', '1722', '09050', '65293', '84245', '011511',
             '102984', '64564', '120145', '20145', '28304', '52771', '107111', '33266', '121157'}

    left = superdic(sig_c)
    left.A2L = {'28304': [{'00105': {'41605', '36831', '12917', '12922'}}], '12917': [{'': set()}],
                '12922': [{'': set()}], '41605': [{'': set()}], '36831': [{'': set()}], '96157': [{'00105': {'36929',
                                                                                                             '36825',
                                                                                                             '36807',
                                                                                                             '36821',
                                                                                                             '36779',
                                                                                                             '36753',
                                                                                                             '36925',
                                                                                                             '36761',
                                                                                                             '12922',
                                                                                                             '37162',
                                                                                                             '36822',
                                                                                                             '12917'}}],
                '37162': [{'': set()}], '36925': [{'': set()}], '36929': [{'': set()}], '36761': [{'': set()}],
                '36753': [{'': set()}], '36822': [{'': set()}], '36779': [{'': set()}], '36807': [{'': set()}],
                '36825': [{'': set()}], '36821': [{'': set()}],
                '5189': [{'00105': {'36901', '36887', '48787', '36900', '12922', '12917'}}], '36887': [{'': set()}],
                '36901': [{'': set()}], '48787': [{'': set()}], '36900': [{'': set()}],
                '39926': [{'00105': {'12917', '54110', '36903', '12922'}, '00114': {'39913', '39914'}}],
                '39914': [{'': set()}], '54110': [{'': set()}], '39913': [{'': set()}], '36903': [{'': set()}],
                '2097': [{'0051': {'17470'}}], '17470': [{'0047': {'3270'}, '0052': {'28597'}}],
                '28597': [{'0052': {'16984', '17210', '16554'}}], '16984': [{'0052': {'28597'}}],
                '17210': [{'': set()}], '16554': [{'': set()}],
                '3270': [{'00105': {'37145', '41408', '37125', '12922'}}], '41408': [{'': set()}],
                '37125': [{'': set()}], '37145': [{'': set()}], '93125': [{'00105': {'12917', '12922'}}],
                '95435': [{'0052': {'18466', '17764'}}], '17764': [{'0052': {'18466'}}], '18466': [{'': set()}],
                '9032': [{'00105': {'36987', '12660', '36988', '36725', '37060', '12922', '37162', '12917'}}],
                '36988': [{'': set()}], '37060': [{'': set()}], '36725': [{'': set()}], '36987': [{'': set()}],
                '12660': [{'': set()}], '8848': [{'00114': {'27705', '36321', '36319'},
                                                  '00105': {'12917', '36987', '37005', '36988', '36725', '38640',
                                                            '12922', '37060', '37004'}}], '37004': [{'': set()}],
                '38640': [{'': set()}], '36321': [{'': set()}], '36319': [{'': set()}], '37005': [{'': set()}],
                '27705': [{'': set()}], '20145': [{'0052': {'16965', '16554', '16701'}}], '16965': [{'': set()}],
                '16701': [{'': set()}], '36047': [{'00105': {'12917', '12922'}}], '38172': [{'00177': {'39596'}}],
                '39596': [{'': set()}]}

    A2L = copy.deepcopy(left.A2L)

    # left.filter()
    # print(left.A2L)
    # left.main('keep_min')
    left.unfold_loops()
    left.sig_c.add("T")
    print(left.sig_c)
    for A in left.sig_c:
        if A != "T" and left.G.has_node(A):
            print("A:,", A)
            print("clusters:", left.clusters(A))
    #left.unfold_path()
    #left.extract_hyper_path()
    # left.unfold_path_A("239877008")
    print('len(left.paths):', len(left.paths))
    print(left.paths)

    # print([len(p) for p in left.paths])

    print("len(left.simple_loops)", len(left.simple_loops))
    # print(left.simple_loops)
    L = [p for p in left.simple_loops if p]
    print(L)
    print(len(L))
    # left.unfold_hyper_path()
    # for A in left.A2L:
    #     if A in sig_c:
    #         print(A)
    #         left.node_history.append(A)
    #         left.role_history.append("")
    #         print(left.unfold_A(A))
