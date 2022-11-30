import os

from pakages.resolution.tools import renew
import copy
import itertools
from src.tools import trans_back


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


class superdic:
    def __init__(self, sig_c=set([]), d_C=set([])):
        # {  A: [ {"": [B_i,....],..., r: [A_j ,...],...}, 
        #          ... 
        #        ]  } 
        self.A2L = {}

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

    # whether dic1 is smaller than dic2
    def super_dic(self, dic1, dic2):
        assert isinstance(dic1, dict)
        assert isinstance(dic2, dict)

        if len(dic1) < len(dic2):
            return False
        else:
            for s in dic2:
                if s not in dic1:
                    return False

            # we need to make sure each (r, B) pair in dic2 is bigger than some (r, A) pair in dic1
            if "" in dic2 and not dic2[""].issubset(dic1[""]):
                return False
            else:
                '''
                for s in dic2:
                    if s != '' and not dic2[s].issubset(dic1[s]):
                        return False
                return True

                '''
                for s in dic2:
                    if s != "":
                        for B in dic2[s]:
                            if B not in dic1[s]:
                                for A in dic1[s]:
                                    if self.super(A, B):
                                        break
                                else:
                                    break
                        else:
                            continue
                        break
                else:
                    return True
                return False

    def super(self, A1_in, A2_in):
        '''return whether A2 is bigger than A1'''
        if self.loops:
            return False
        if isinstance(A1_in, tuple):
            A1 = A1_in[0]
        else:
            A1 = A1_in

        if isinstance(A2_in, tuple):
            A2 = A2_in[0]
        else:
            A2 = A2_in

        if A1 == A2:
            return True

        assert A1 in self.A2L or A1 in self.sig_c
        assert A2 in self.A2L or A2 in self.sig_c

        if A2 not in self.A2L:
            if A1 in self.A2L and '' in self.A2L[A1][0] and A2 in self.A2L[A1][0]['']:
                return True
            else:
                return False
        elif self.A2L[A2] == [{'': set()}] or self.A2L[A2] == [{'': {()}}]:
            return True

        if A1 in self.A2L:
            if self.A2L[A2] == [{'': set()}] or self.A2L[A2] == [{'': {()}}]:
                return False

        if A1 in self.sig_c and A1 not in self.A2L:
            for dic in self.A2L[A2]:
                if len(dic) == 1 and "" in dic and dic[""] == {A1}:
                    return True

        if A1 in self.A2Super and A2 in self.A2Super[A1]:
            return True
        if A1 in self.A2NoSuper and A2 in self.A2NoSuper[A1]:
            return False

        # first check if every r in follower of A1 is in follower of A2
        # we assume the Si in self.A2L[A] is order by the number of their keys !!!!
        # we need make sure for each dic in self.A2L[A2], there exists a smaller dic1 in self.A2L[A1]

        if A1 not in self.A2L:
            assert A1 in self.sig_c
            list1, list2 = [{"": {A1}}], self.A2L[A2]
        else:
            list1, list2 = self.A2L[A1], self.A2L[A2]
        len1, len2 = len(list1), len(list2)
        i, j = 0, len2 - 1

        if (A1, A2) in self.super_history:
            self.loops = True
            return False
        else:
            self.super_history.append((A1, A2))

        i2j = {}
        while i < len1:
            if j < 0:
                renew(self.A2NoSuper, A1, A2)
                assert self.super_history[-1] == (A1, A2)
                self.super_history.pop()
                return False
            dic1, dic2 = list1[i], list2[j]
            if len(dic1) < len(dic2):
                renew(self.A2NoSuper, A1, A2)
                assert self.super_history[-1] == (A1, A2)
                self.super_history.pop()
                return False
            else:
                for s in dic2:
                    if s not in dic1:
                        j -= 1
                        break
                else:
                    if "" in dic2 and not dic2[""].issubset(dic1[""]):
                        j -= 1
                    else:
                        i2j[i] = j
                        i += 1

        # then check through all elements
        i = 0
        while i < len1:
            j = i2j[i]
            result = self.super_dic(list1[i], list2[j])
            if result:
                i += 1
            else:
                j -= 1
                if j < 0:
                    renew(self.A2NoSuper, A1, A2)
                    assert self.super_history[-1] == (A1, A2)
                    self.super_history.pop()
                    return False

        renew(self.A2Super, A1, A2)
        assert self.super_history[-1] == (A1, A2)
        self.super_history.pop()
        return True

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

    def unfold_A(self, A):
        # return if there exists non-trivial loops
        if self.nontrivial_loops:
            return {}

        if A in self.sig_c:
            result = {f"<{A}>": []}
        else:
            result = {}

        f_loops = False

        if A not in self.A2L:
            return result
        for dic in self.A2L[A]:
            pools = []
            l_dic = sum([len(dic[r]) for r in dic])
            for r in dic:
                f_break = False
                for B in dic[r]:
                    if B in self.node_history:
                        id = self.node_history.index(B)
                        # return if there exists non-trivial loops
                        if set(self.role_history[id:]) != {""}:
                            self.nontrivial_loops = True
                            return {}
                        # ignore trivial loops
                        else:
                            f_break = True
                            break

                    self.node_history.append(B)
                    self.role_history.append(r)
                    pi = []
                    dic_B = self.unfold_A(B)

                    if dic_B:
                        if r != "":
                            if A in self.definite_C:
                                new_term = ("h", A, r, B)
                            else:
                                new_term = ("r", A, r, B)
                        else:
                            if l_dic > 1:
                                new_term = ("h", A, r, B)
                            else:
                                new_term = ("r", A, r, B)

                        for k, v in dic_B.items():
                            if f_loops:
                                self.nontrivial_loops = True

                            if not v:
                                new_value = [{new_term}]
                            else:
                                new_value = []
                                for s in v:
                                    s.add(new_term)
                                    new_value.append(s)

                            if r == "":
                                new_k = k
                            else:
                                new_k = f"(some <{r}> {k})"

                            pi.append((new_k, new_value))

                        pools.append(pi)
                    else:
                        f_break = True
                        break

                    self.node_history.pop()
                    self.role_history.pop()

                if f_break:
                    break
            else:
                assert pools
                for pi in itertools.product(*pools):
                    pi_sorted = sorted(list({p[0] for p in pi}))
                    if len(pi_sorted) > 1:
                        new_key = "(and " + " ".join(pi_sorted) + ' )'
                        value_pools = [p[1] for p in pi]
                        new_val = []
                        for vals in itertools.product(*value_pools):
                            va = set([])
                            for s in vals:
                                va.update(s)
                            new_val.append(va)
                        if new_key in result:
                            result[new_key] += new_val
                        else:
                            result[new_key] = new_val
                    else:
                        new_key = pi[0][0]
                        if new_key in result:
                            result[new_key] += pi[0][1]
                        else:
                            result[new_key] = pi[0][1]

        return result

    def cut_redundancy_right(self, L):
        if len(L) <= 1:
            return [{l} for l in L]

        path_elk = "pakages/elk-tools"
        f1 = open(path_elk + "/test.owl", 'w')
        f1.write("Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\nOntology(\n")
        id2key = {}
        for i, p in enumerate(L):
            f1.write(trans_back(f"(equivalent <N{i}> {p})\n"))
            id2key[str(i)] = p
        f1.write(")\n")
        f1.close()

        command = f"java -jar {path_elk}/elk-standalone.jar --i {path_elk}/test.owl  -c -o {path_elk}/taxonomy.owl"
        os.system(command)

        filter_collect = equi_sets()
        filter_collect.collection = [{l} for l in L]
        with open(f"{path_elk}/taxonomy.owl", 'r') as f:
            d = f.readlines()
            for l in d:
                l_s = l.split("<N")
                if len(l_s) > 2:
                    if l[0] == "S":
                        assert len(l_s) == 3
                        A, B = id2key[l_s[1].split(">")[0]], id2key[l_s[2].split(">")[0]]
                        filter_collect.add_unequal(A, B)
                    elif l[0] == 'E':
                        s = {id2key[li.split(">")[0]] for li in l_s[1:]}
                        filter_collect.add_equal(s)

        return filter_collect.get_result()

    def unfold_hyper_path(self):
        L = []
        for A in self.sig_c:
            self.nontrivial_loops = False
            self.node_history.append(A)
            self.role_history.append("")
            r_A = self.unfold_A(A)
            self.node_history = []
            self.role_history = []
            # return if there exists non-trivial loops
            if self.nontrivial_loops:
                print("!!!!!It conatins non-trivial loops!!!!! skiped!!!!!")
                return
            del r_A[f"<{A}>"]

            result = self.cut_redundancy_right(r_A.keys())
            result_keys = set([])
            for s in result:
                if len(s) > 1:
                    for si in s[1:]:
                        r_A[s[0]] += r_A[si]
                    result_keys.add(s[0])
                else:
                    result_keys.update(s)

            del_keys = set(r_A.keys()) - result_keys
            for k in del_keys:
                del r_A[k]

            L.append(len(r_A))
            if r_A:
                self.r_paths.append((A, r_A))
        # print("self.r_paths:", self.r_paths)

        self.nontrivial_loops = False
        print("********************unfolded length:", sum(L))

    def clear(self):
        self.A2L = {}

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

    def size(self):
        l = 0
        for A in self.A2L:
            for dic in self.A2L[A]:
                for r in dic:
                    for e in dic[r]:
                        if isinstance(e, tuple):
                            l += len(e)
                        else:
                            l += 1

        return str(l)

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
    sig_c = {'26564', '19405'}

    left = superdic(sig_c)
    left.A2L = {'26564': [{'0037': {'21198', '19536', '26565', '16702', '19405', '16945'}}], '21198': [{'': set()}],
                '16945': [{'': set()}], '26565': [{'': {'19405'}, '0032': {'492'}}], '492': [{'': set()}],
                '19536': [{'': set()}], '16702': [{'': set()}]}

    # left.filter()
    print(left.A2L)
    # left.main('keep_min')
    print(left.super('26565', '19405'))
    print(left.super('19405', '26565'))
    # print(f)
    # print(left.super('16710', '17930'))
    left.main('keep_min')
    print(left.A2L)
    print(left.A2L.keys())
    print(len(left.A2L.keys()))

    # left.unfold_hyper_path()
    # for A in left.A2L:
    #     if A in sig_c:
    #         print(A)
    #         left.node_history.append(A)
    #         left.role_history.append("")
    #         print(left.unfold_A(A))
