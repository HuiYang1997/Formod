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


class cluster:
    def __init__(self, ):
        # {  A: {"": [B_i,....],..., r: [A_j ,...],...},
        #     ...
        #    }
        self.A2L = {}

        self.sig_c = set()

        self.super_history = []
        self.loops_pairs = set([])
        self.pairs_before_loops = set([])

        self.A2Super = {}
        self.A2NoSuper = {}

    def add(self, A, r, B):
        if A in self.A2L:
            if r in self.A2L[A]:
                self.A2L[A][r].add(B)
            else:
                self.A2L[A][r] = {B}
        else:
            self.A2L[A] = {r: {B}}

    # whether dic1 is smaller than dic2
    def super_dic(self, dic1, dic2):
        # the input satisifies : 1. len(dic1) >= len(dic2) and set(dic2.keys()).issubset(set(dic1.keys())) ;
        # 2. "" not in dic2 or dic2[""].issubset(dic1[""])"
        for s in dic2:
            if s != "":
                for B in dic2[s]:
                    if B not in dic1[s]:
                        for A in dic1[s]:
                            if self.super(A, B):
                                # print('super', A, B)
                                break
                        else:
                            break
                else:
                    continue
                break
        else:
            return True

        return False

    def super(self, A1, A2):
        '''return whether A2 is bigger than A1'''
        if A1 == A2:
            return True
        elif A2 not in self.A2L and A2 not in self.sig_c:  # A2--> T
            return True
        elif A1 not in self.A2L and A1 not in self.sig_c:  # A1--> T
            return False
        elif A1 in self.A2Super and A2 in self.A2Super[A1]:
            return True
        elif A1 in self.A2NoSuper and A2 in self.A2NoSuper[A1]:
            return False


        # check if one of Ai is in signature
        if A2 in self.sig_c or A1 in self.sig_c:
            if A1 in self.A2L and '' in self.A2L[A1] and A2 in self.A2L[A1]['']:
                return True
            elif A2 in self.A2L and self.A2L[A2] == {'': {A1}}:
                return True
            else:
                return False
        else:
            # check if not
            dic1, dic2 = self.A2L[A1], self.A2L[A2]

            if (A1, A2) in self.super_history:
                self.loops_pairs.add((A1, A2))
                self.pairs_before_loops.update(self.super_history)
                return False
            else:
                self.super_history.append((A1, A2))

                if len(dic1) >= len(dic2) and set(dic2.keys()).issubset(set(dic1.keys())):
                    if "" not in dic2 or dic2[""].issubset(dic1[""]):
                        if self.super_dic(dic1, dic2):
                            renew(self.A2Super, A1, A2)
                            assert self.super_history[-1] == (A1, A2)
                            self.super_history.pop()
                            return True

                renew(self.A2NoSuper, A1, A2)
                assert self.super_history[-1] == (A1, A2)
                self.super_history.pop()
                return False

    def filter_ConceptInSameRole(self):
        A2L_new = {}
        for A in self.A2L:
            dic = self.A2L[A]
            new_dic = {}
            for r in dic:
                concepts_correspond2r = dic[r]
                if len(concepts_correspond2r) == 1:
                    new_dic[r] = concepts_correspond2r
                    continue
                equal_c = equi_sets()
                redundant_c = set([])
                smaller_c = set([])
                for c1, c2 in itertools.combinations(concepts_correspond2r, 2):
                    f = False
                    self.super_history = []
                    if self.super(c1, c2) and (c1, c2) not in self.pairs_before_loops:
                        redundant_c.add(c2)
                        f = True

                    self.super_history = []
                    if self.super(c2, c1) and (c2, c1) not in self.pairs_before_loops:
                        redundant_c.add(c1)
                        if f:
                            equal_c.add(c1, c2)
                        elif (c1, c2) not in self.pairs_before_loops:
                            smaller_c.add(c1)
                    elif (c2, c1) not in self.pairs_before_loops:
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
                    filter_conceptes.update(tuple(equal_c_filtered))
                assert filter_conceptes
                new_dic[r] = filter_conceptes
            A2L_new[A] = new_dic

        self.A2L = A2L_new

    def transfer2C(self, k, r_res=None, k_res=None, history=set()):
        if r_res and k not in self.A2L:
            return ""
        elif k in self.sig_c and not r_res:
            return f"<{k}>"
        elif k not in self.A2L and not r_res:
            return "owl:Thing"
        elif k in history:
            return "owl:Thing"
        else:
            concepts = []
            for r in self.A2L[k]:
                if not r_res or r == r_res:
                    if r == '':
                        concepts += [f'<{B}>' for B in self.A2L[k][r]]
                    else:
                        for k_next in self.A2L[k][r]:
                            if not k_res or k_next == k_res:
                                if isinstance(k_next, tuple):
                                    concepts.append(f'(some <{r}> {self.transfer2C(k_next[0], history=history | {k})})')
                                else:
                                    assert isinstance(k_next, str)
                                    concepts.append(f'(some <{r}> {self.transfer2C(k_next, history=history | {k})})')
            if not r_res:
                if len(concepts) == 1:
                    return " ".join(concepts)
                else:
                    return f'(and {" ".join(sorted(concepts))})'
            else:
                return concepts

    def clear(self):
        self.A2L = {}

        self.sig_c = set([])

        self.super_history = []
        self.loops_pairs = set([])
        self.pairs_before_loops = set([])

        self.A2Super = {}
        self.A2NoSuper = {}

    def delete_non_reachable_keys(self, start_keys):
        keys = set(start_keys)
        while True:
            new_keys = set()
            for k in keys & self.A2L.keys():
                for r in self.A2L[k]:
                    new_keys.update(self.A2L[k][r])
            if not new_keys.issubset(keys):
                keys.update(new_keys)
            else:
                break

        print(f"delete {len(self.A2L.keys()-keys)} keys")
        for k in self.A2L.keys()-keys:
            del self.A2L[k]

        return


    # keep only maximal(or min) element of A
    def main(self, source_node_set):
        print('delete non reachable keys:')
        self.delete_non_reachable_keys(source_node_set)

        self.filter_ConceptInSameRole()

        Empty_A = {A for A in self.A2L if self.A2L[A] == [{'': {()}}] or self.A2L[A] == [{"": set()}]}
        for A in Empty_A:
            del self.A2L[A]
