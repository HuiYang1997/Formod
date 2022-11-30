from halp.directed_hypergraph import DirectedHypergraph
from itertools import product
from multiprocessing import Pool

def replace(l1, l2, A):
    result = []

    for C1, C2 in product(l1, l2):
        new_C = {a.replace(A, C1) for a in C2 if a != A}
        if A in C2:
            new_C.update(C1)

        result.append(frozenset(new_C))
    return result


class subH(DirectedHypergraph):
    def __init__(self):
        super().__init__()
        # Assume each edge has attributes:
        # {"head": {head, C}, "tail": {n1, n2...}, "concept": C}
        # where C = [C1,..., Cn], Ci is the conjunct of C, Ci = {"r":[Ci_1,..., Ci_m]} or Ai
        # assert tail not in C!!!

        self.subH_id_inferences = {}

        # record e_id --> subsumptions
        self.id2subsumptions = {}

        self.loop_h_id = set()

        self.initial_size = 0

        self.nodes2degree = {}

    def renew_degree(self, nodes):
        for n in nodes:
            if n in self.nodes2degree:
                if self.has_node(n):
                    self.nodes2degree[n] = len(self.get_forward_star(n)) * len(self.get_backward_star(n))
                else:
                    del self.nodes2degree[n]
        return

    def get_minimal_nodes(self):
        # return key of self.nodes2degree with the smallest value
        return min(self.nodes2degree, key=self.nodes2degree.get)

    def forget_one(self, A, delete_type="all"):
        # forget one node A
        e_forward = self.get_forward_star(A)
        e_backward = self.get_backward_star(A)

        nodes_to_renew = set()

        for e_f, e_b in product(e_forward, e_backward):
            if e_b == e_f:
                # only happend if e_b represent a non-trivial loops
                self.loop_h_id.add(e_b)
                tail = [n for n in self.get_hyperedge_tail(e_b) if n != A]
                nodes_to_renew.update(tail)
                print('find loop:', self.get_hyperedge_attributes(e_b))
                continue

            # resolution ==> build new edge from e_b, e_f
            new_tail = self.get_hyperedge_tail(e_b)
            new_tail.update(self.get_hyperedge_tail(e_f))
            new_tail.remove(A)
            nodes_to_renew.update(new_tail)

            concept_f = self.get_hyperedge_attribute(e_f, 'concept')
            new_head = [n for n in self.get_hyperedge_head(e_f) if n[0] != '(' and n[0] != '<'][0]
            nodes_to_renew.add(new_head)

            # print(new_head)
            assert len([n for n in self.get_hyperedge_head(e_f) if n[0] != '(' and n[0] != '<']) == 1

            concept_b = self.get_hyperedge_attribute(e_b, 'concept')

            if f'<{new_head}>' not in concept_b:
                new_concept_list, new_C = self.replace(concept_f, f"<{A}>", concept_b)
                if len(new_C) == 1:
                    new_concept = new_concept_list[0]
                else:
                    new_concept = f"(and {' '.join(new_concept_list)})"
                # new_C = [a.replace(f"<{A}>", b_c) for a in concept_f if a != f"<{A}>"]
                # if f"<{A}>" in concept_f:
                #     for C_b in concept_b:
                #         if C_b not in new_C:
                #             new_C.append(C_b)
                # new_C.sort()
                #
                # if len(new_C) > 1:
                #     new_concept = f'(and {" ".join(new_C)})'
                # else:
                #     new_concept = new_C[0]

                # add new edge if not exist
                try:
                    self.get_hyperedge_id(new_tail, {new_head, new_concept})
                except ValueError:
                    self.add_hyperedge(new_tail, {new_head, new_concept}, {'concept': new_C})
                    
                new_id = self.get_hyperedge_id(new_tail, {new_head, new_concept})
                # record as inferences
                if new_id in self.subH_id_inferences:
                    self.subH_id_inferences[new_id].append([e_b, e_f])
                else:
                    self.subH_id_inferences[new_id] = [[e_b, e_f]]

        if delete_type == 'all':
            self.remove_node(A)
        elif delete_type == 'forward':
            self.remove_hyperedge(e_forward)
        elif delete_type == 'backward':
            self.remove_hyperedge(e_backward)

        self.renew_degree(nodes_to_renew)
        return

    def forget(self, preserve_nodes, delete_type="all"):
        # initialize self.nodes2degree
        self.nodes2degree = {n: len(self.get_forward_star(n)) * len(self.get_backward_star(n)) for n in
                             self.node_iterator() if n[0] != '(' and n[0] != '<' and n not in preserve_nodes}

        # forget all nodes with degree 0
        nodes_to_delete = set()
        for A in self.nodes2degree:
            if self.nodes2degree[A] == 0:
                self.forget_one(A, delete_type)
                nodes_to_delete.add(A)

        for A in nodes_to_delete:
            del self.nodes2degree[A]

        # forget rest nodes
        print('node_to_forget:', len(self.nodes2degree))
        while self.nodes2degree:
            A = self.get_minimal_nodes()
            if self.nodes2degree[A] > 50:
                assert self.has_node(A)
                self.delete_redundant_edges([A])

            self.forget_one(A, delete_type)
            if A in self.nodes2degree:
                del self.nodes2degree[A]

        # delete redundant edges
        self.delete_redundant_edges(preserve_nodes)

        return

    def delete_redundant_edges(self, preserve_nodes):
        # delete redundant edges
        for n in preserve_nodes:
            if self.has_node(n):
                concepts_n = [(e, self.get_hyperedge_attribute(e, 'concept')) for e in self.get_backward_star(n)]
                concepts_n.sort(key=lambda x: len(x[1]))
                deleted_edges = set()
                for i in range(len(concepts_n)):
                    e_i, c_i = concepts_n[i]
                    for j in range(i):
                        e_j, c_j = concepts_n[j]
                        if e_j not in deleted_edges:
                            if all(x in c_i for x in c_j):
                                #if self.smaller(c_j, c_i):
                                deleted_edges.add(e_i)
                                break

                for e in deleted_edges:
                    self.remove_hyperedge(e)

        return

    def smaller(self, c_i, c_j):
        if c_i == c_j:
            return True

        for x in c_i:
            if isinstance(x, str):
                if x in c_j:
                    continue
                else:
                    return False
            else:
                for x_j in c_j:
                    if isinstance(x_j, dict):
                        for r in x.keys() & x_j.keys():
                            if self.smaller(x[r], x_j[r]):
                                break
                        else:
                            continue
                        break
                else:
                    return False

                continue

        return True

    def replace(self, C_0, A, C_new):
        result_C = []
        result_concept_list = []
        for conjunct_0 in C_0:
            if isinstance(conjunct_0, str):
                if conjunct_0 != A:
                    result_C.append(conjunct_0)
                    result_concept_list.append(conjunct_0)
                else:
                    for conjunct_new in C_new:
                        if conjunct_new not in C_0:
                            result_C.append(conjunct_new)
                    concept_new_list, _ = self.replace(C_new, '<>', [])
                    result_concept_list.extend(concept_new_list)
            else:
                assert len(conjunct_0) == 1
                for r in conjunct_0:
                    concept_r_list, C_r = self.replace(conjunct_0[r], A, C_new)
                    result_C.append({r: C_r})
                    if len(concept_r_list) == 1:
                        result_concept_list.append(f"(some {r} {concept_r_list[0]})")
                    else:
                        result_concept_list.append(f"(some {r} (and {' '.join(concept_r_list)}))")

        return sorted(list(set(result_concept_list))), result_C

