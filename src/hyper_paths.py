import copy
import os
from itertools import product
from src.tools import trans_back
import line_profiler


def cut_axiom(one_axiom):
    l, i = len(one_axiom), 0
    result_str, result, type_1 = '', [], 'outside'
    while i < l:
        if type_1 == 'outside':
            if one_axiom[i] == '(':
                type_1 = 'inside'
                i += 1
            else:
                result_str += one_axiom[i]
                i += 1
        else:
            count, count_term_1, start_id = 0, 1, i
            while i < l:
                if one_axiom[i] == '(':
                    count_term_1 += 1
                elif one_axiom[i] == ')':
                    count_term_1 -= 1
                    if count_term_1 == 0:
                        result.append(one_axiom[start_id:i])
                        result_str += '*'
                        i += 1
                        type_1 = 'outside'
                        break
                i += 1
    final_result = []
    for C in result_str.split('*'):
        if C[0] != "(":
            final_result += C.split(' ')
        else:
            final_result.append(C)
    return final_result


class hyperpaths:
    def __init__(self, source):
        self.h_paths = {}
        self.source = source

    def unfold(self, e_start, E, e2r):
        result = []
        if e_start in e2r:
            r = e2r[e_start]
        else:
            r = ""

        e_r_pairs = {(e_start, r)}
        for ei in E[e_start]:
            if ei[0] != 'e':
                result.append(ei)
            else:
                result_i, e_r_pairs_i = self.unfold(ei, E, e2r)
                e_r_pairs.update(e_r_pairs_i)
                if isinstance(result_i, list):
                    result += result_i
                else:
                    result.append(result_i)

        if r == 'h' or "":
            return result, e_r_pairs
        else:
            return {r: result}, e_r_pairs

    def add_h(self, C, e_r_pairs, type = 'add'):
        if type == 'add':
            assert isinstance(e_r_pairs, set)
        else:
            assert isinstance(e_r_pairs, list)

        if C in self.h_paths:
            if type == 'add':
                self.h_paths[C].append(e_r_pairs)
            else:
                self.h_paths[C] = e_r_pairs
        else:
            if type == 'add':
                self.h_paths[C] = [e_r_pairs]
            else:
                self.h_paths[C] = e_r_pairs
        return

    def add(self, e_start, E, E2id):
        # E: {e_1:{e_2,...., e_n}, e_2:{...}, ... , e_k:{n1, n2, e_n}, ...}, ni in signature
        # E2id: {e: { r: {h_id, ... }, ...}
        list_E = [e for e in E2id if e in E]
        list_r = [E2id[e].keys() for e in list_E]
        for choice_r in product(*list_r):
            e2r = {list_E[i]: choice_r[i] for i in range(len(list_E))}
            d, e_r_pairs = self.unfold(e_start, E, e2r)
            C = self.transfer_d2C(d)
            print(d, C)
            self.add_h(C, e_r_pairs)

    def transfer_d2C(self, d):
        C = ''
        atomic_conjunct = set()
        for k in d:
            if isinstance(d, dict):
                assert len(d) == 1
                return f'(some <{k}> {self.transfer_d2C(d[k])})'
            else:
                assert isinstance(d, list)
                if isinstance(k, str):
                    atomic_conjunct.add(k)
                else:
                    assert isinstance(k, dict)
                    atomic_conjunct.add(self.transfer_d2C(k))

        C += f" <{'> <'.join(sorted(list(atomic_conjunct)))}>"

        if len(atomic_conjunct) == 1:
            return C[1:]
        else:
            return f'(and{C})'

    # @profile
    def main(self):
        if len(self.h_paths) <= 1:
            self.valid_indexs = (0)
            return

        path_elk = "pakages/elk-tools"
        f1 = open(path_elk + "/test.owl", 'w')
        f1.write("Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\nOntology(\n")
        i2C = {}
        all_index = {f'N{k}' for k in range(len(self.h_paths))}
        for i, C in enumerate(self.h_paths.keys()):
            f1.write(trans_back(f"(equivalent <N{i}> {C})\n"))
            i2C[f'N{i}'] = C
            if len(C.split('<')) < 3:
                all_index.add(C[1:-1])
        f1.write(")\n")
        f1.close()

        command = f"java -jar {path_elk}/elk-standalone.jar --i {path_elk}/test.owl  -c -o {path_elk}/taxonomy.owl"
        os.system(command)

        del_ind = set()
        equal_inds = []
        with open(f"{path_elk}/taxonomy.owl", 'r') as f:
            d = f.readlines()
            for l in d:
                l_s = l.split("<")
                if len(l_s) > 2:
                    if l[0] == "S":
                        assert len(l_s) == 3
                        A, B = l_s[1].split(">")[0], l_s[2].split(">")[0]
                        if B in all_index:
                            del_ind.add(A)
                    elif l[0] == 'E':
                        s = {(li.split(">")[0]) for li in l_s[1:]}
                        equal_inds.append(s)

        rest_C = set()
        for s in equal_inds:
            all_index -= s
            if not s & del_ind:
                rest_C.update({i2C[j] for j in s if j[0] == 'N'})

        all_index -= del_ind
        for j in all_index:
            if j[0] == 'N':
                rest_C.add(i2C[j])

        for C in set(self.h_paths.keys()) - rest_C:
            del self.h_paths[C]
        return

    def num_paths(self):
        l = 0
        for C in self.h_paths:
            l += len(self.h_paths[C])

        return l

def tensor_product(Ls):
    result = []
    for S in product(*Ls):
        new_s = set()
        for si in S:
            assert 'e' not in si
            new_s.update(si)

        result.append(new_s)

    return result


def integrate_hyperpaths(hyperpath_list, new_r_dic, h_A_id, last_edge):
    def delete_and(s):
        if s[:5] == "(and ":
            return s[5:-1]
        else:
            return s

    for new_r in new_r_dic:
        new_edges = {(h_A_id, new_r)}
        new_edges.update(last_edge)
        if len(hyperpath_list) > 1:
            assert new_r == 'h'
            C_list = [list(h.h_paths.keys()) for h in hyperpath_list]
            for C_pairs in product(*C_list):
                new_e_r_pairs = tensor_product([hyperpath_list[i].h_paths[C_pairs[i]] for i in range(len(C_pairs))] + [[new_edges]])
                new_C_pairs = {""}

                for C in C_pairs:
                    new_C_pairs.update(cut_axiom(delete_and(C)))
                new_C_pairs.remove("")
                # print("new_C_pairs:", new_C_pairs)
                if not new_C_pairs:
                    # print(C_pairs, new_C_pairs)
                    new_C = '<owl:Thing>'
                elif len(new_C_pairs) == 1:
                    C_0 = list(new_C_pairs)[0]
                    # print(C_0)
                    assert C_0[0] == '(' or len(C_0.split(" ")) == 1

                    if C_0[0] == "(" or len(C_0.split(" ")) == 1:
                        new_C = C_0
                    else:
                        new_C = f'(and {" ".join(new_C_pairs)})'
                else:
                    new_C = f'(and {" ".join(new_C_pairs)})'

                yield new_C, new_e_r_pairs
        else:
            assert new_r != ' '
            h = hyperpath_list[0]
            if new_r == " ":
                for C in h.h_paths:
                    new_paths = tensor_product([h.h_paths[C]] + [[new_edges]])
                    yield C, new_paths
            else:
                assert new_r != 'h'
                for C in h.h_paths:
                    new_C = f'(some <{new_r}> {C})'
                    new_paths = tensor_product([h.h_paths[C]] + [[new_edges]])
                    yield new_C, new_paths


if __name__ == "__main__":
    e_start = 'e1'
    E = {"e1": {"e2", "e3"}, "e2": {"e4"}, "e3": {"e6"}, "e4": {"1", "2"}, "e6": {"1", "2"}}
    e2r = {"e1": "h", "e2": "r", "e3": "r", "e4": "h", "e6": "h"}
    H = hyperpaths('A')
    d, e_r_pairs = H.unfold(e_start, E, e2r)
    print(d, e_r_pairs)
