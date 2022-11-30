import copy

from halp.directed_hypergraph import DirectedHypergraph
from src.resolution_over_hypergraph import subH
from queue import Queue
import line_profiler
from tqdm import tqdm


class Direct_hyper_graph(DirectedHypergraph):
    def __init__(self):
        super().__init__()
        # can be viewed as "node--> node_next"
        self.subsumptions = {}

        # set of hyperedges_id in the subgraph extract by signature
        self.subgraph_sig = subH()

        # record "node_next--> node" for tracing backward phase
        self.nn = {}

        # nodes (not in sig_c) that should consider as the start of a cluster
        self.node_start = set()

        # axioms that appear on the left side more than once
        self.concept_non_terminology = set()

        self.sig_c = set()
        self.sig_r = set()

        self.axioms_id = set()

    def clear(self):
        self.subgraph_sig = subH()
        self.nn = {}
        self.node_start = set()

        self.axioms_id = set()

    def add_edge(self, head, tail, attribute={}):  # attributes : role --> axioms_id
        try:
            h_id = self.get_hyperedge_id(tail, head)
            new_attribute = {**self.get_hyperedge_attributes(h_id), **attribute}
            self.add_hyperedge(head, tail, new_attribute)
        except ValueError:
            self.add_hyperedge(head, tail, attribute)

        return

    def get_forward_edges(self, node):
        if self.has_node(node):
            yield node, iter(self.get_forward_star(node))

        if node in self.subsumptions:
            for node_next in self.subsumptions[node]:
                assert node_next != node
                # only allow simple edges A-->B for
                # (i) A in signature ;
                # or (ii) A appears on the left of axioms more than once
                if node not in self.sig_c and node not in self.concept_non_terminology:
                    continue
                if self.has_node(node_next) and self.get_forward_star(node_next):
                    if node_next in self.nn:
                        self.nn[node_next].add(node)
                    else:
                        self.nn[node_next] = {node}

                    yield node_next, iter(self.get_forward_star(node_next))

    def renew_subgraph_sig(self, tail, head, role='h', axiom_id=None):
        if role == 'h' or role == '':
            new_concept = [f'<{t}>' for t in tail]
            if len(new_concept) > 1:
                head.add(f'(and {" ".join(sorted(new_concept))})')
            else:
                head.add(new_concept[0])
        else:
            assert len(tail) == 1
            new_concept = [{f'<{role}>': [f'<{t}>' for t in tail]}]
            head.add(f'(some <{role}> <{"".join(tail)}>)')


        self.subgraph_sig.add_hyperedge(tail, head, {'concept': new_concept})
        sub_h_id = self.subgraph_sig.get_hyperedge_id(tail, head)

        # axiom_id is "None" when it is not corresponding to an axiom in ontology
        if axiom_id:
            self.subgraph_sig.subH_id_inferences[sub_h_id] = [[axiom_id]]
            self.axioms_id.add(axiom_id)

        return

    def traverse_forward(self, source_nodes, flag_add=True):
        if not isinstance(self, DirectedHypergraph):
            raise TypeError("Algorithm only applicable to directed hypergraphs")

        # Pe consist of tracked hyperedges id
        Pe = set([])
        # union of value of self.nn
        union_start = set()
        # Explicitly tracks the set of visited nodes
        visited_nodes = set()
        valid_nodes = set()

        # for n in source_nodes:
        #     self.nn[n] = {n}

        Q = Queue()
        for n in source_nodes:
            Q.put(n)

        # traverse all hyperedge and r-edge
        while not Q.empty():
            current_node = Q.get()
            # At current_node, we can traverse each hyperedge in its forward star
            for node_next, forward_star_iter in self.get_forward_edges(current_node):
                if node_next in visited_nodes:
                    continue

                f_add = False
                for hyperedge_id in forward_star_iter:
                    if hyperedge_id in Pe:
                        continue
                    else:
                        union_start.add(current_node)
                        attributes = self.get_hyperedge_attributes(hyperedge_id)
                        new_attributes = {k: attributes[k] for k in attributes if k in self.sig_r or k == 'h'}
                        head_node = list(attributes['head'])[0]
                        if head_node != current_node:
                            if current_node not in self.subsumptions or head_node not in self.subsumptions[current_node]:
                                f_add = True
                        if new_attributes:
                            new_tail_nodes = attributes['tail']
                            if set(new_tail_nodes) - valid_nodes == {node_next}:
                                Pe.add(hyperedge_id)

                                if len(new_tail_nodes) == 1:
                                    self.node_start.add(head_node)

                                # Traversing a hyperedge in current_node's forward star yields
                                # the set of head nodes of the hyperedge; visit each head node
                                if head_node not in self.sig_c and flag_add:
                                    self.node_start.add(head_node)
                                if head_node not in visited_nodes and head_node != current_node:
                                    Q.put(head_node)
                if f_add:
                    valid_nodes.add(node_next)
                visited_nodes.add(node_next)
            visited_nodes.add(current_node)

        self.node_start.update(self.sig_c)
        return union_start, Pe

    def get_backward_edges(self, node):
        if self.has_node(node):
            yield node, iter(self.get_backward_star(node))

        if node in self.nn:
            for node_pre in self.nn[node]:
                assert node_pre != node
                if self.has_node(node_pre) and node_pre not in self.sig_c:  # here we do not trace forward beyond nodes in signature
                    yield node_pre, iter(self.get_backward_star(node_pre))

    def traverse_backward(self, source_node_set, Pe):
        visited_node_set = set()
        for source_node in source_node_set:
            visited_node_set.update(self.traverse_backward_one_node(source_node, Pe))

        return visited_node_set

    def filter_hyper_edges(self, Pe):  # only works for H (not G)!!!
        # in this step, we filter all redundant hyper_edges (A_1, ...., A_n) --> A in the sense that:
        # There is a minimal subset (e.g. S_1) over all S_i = {B,...} such that B--> A_i.
        # It means that B--> A, the derivation of which is contained in the justifications, for all B in S_1
        valid_edges = set()

        for h_id in Pe:
            tail = self.get_hyperedge_tail(h_id)
            if len(tail) == 1:
                valid_edges.add(h_id)
            else:
                # print([self.nn[t] for t in tail])
                for i, t in enumerate(tail):
                    if t in self.nn:
                        t_pre = self.nn[t]
                    else:
                        t_pre = {t}
                    new_term = t_pre & self.node_start
                    if i == 0:
                        intersection = new_term
                        L = len(intersection)
                    else:
                        if L > len(new_term):
                            L = len(new_term)

                        intersection &= t_pre
                        if L > len(intersection):
                            valid_edges.add(h_id)
                            break

        return valid_edges

    def traverse_backward_one_node(self, source_node, avaliable_edges):
        # Explicitly tracks the set of visited nodes
        visited_nodes = set()

        Q = Queue()
        Q.put(source_node)

        while not Q.empty():
            current_node = Q.get()
            # At current_node, we can traverse each hyperedge in its forward star
            for node_pre, backward_star_iter in self.get_backward_edges(current_node):
                if (current_node, node_pre) in visited_nodes:
                    continue
                for hyperedge_id in backward_star_iter:
                    if hyperedge_id in avaliable_edges:
                        # Traversing a hyperedge in current_node's forward star yields
                        # the set of head nodes of the hyperedge; visit each head node
                        tail_node_set = self.get_hyperedge_tail(hyperedge_id)
                        if current_node not in tail_node_set or len(tail_node_set) == 1:
                            for key in self.get_hyperedge_attributes(hyperedge_id):
                                if key == 'h' or key in self.sig_r:
                                    axiom_id = self.get_hyperedge_attribute(hyperedge_id, key)
                                    self.renew_subgraph_sig(tail_node_set, {node_pre}, key, axiom_id)
                            for tail_node in tail_node_set:
                                if tail_node not in visited_nodes:
                                    Q.put(tail_node)
                visited_nodes.add((current_node, node_pre))
            visited_nodes.add(current_node)

        return visited_nodes

    # @profile
    def enumerate_hyper_paths(self, preserve_nodes, flag_first=True, delete_type='all'):
        if flag_first:
            # add subsumptions
            for n in self.nn.keys():
                for n_pre in self.nn[n]:
                    self.subgraph_sig.add_hyperedge({n_pre}, {n, f'<{n_pre}>'}, {'concept': [f'<{n_pre}>']})
                    e_id = self.subgraph_sig.get_hyperedge_id({n_pre}, {n, f'<{n_pre}>'})
                    self.subgraph_sig.id2subsumptions[e_id] = (n_pre, n)

            self.subgraph_sig.initial_size = len(self.subgraph_sig.get_hyperedge_id_set())

        # compute hyper-paths by forgetting
        # nodes_set = [(n, len(self.subgraph_sig.get_forward_star(n)) * len(self.subgraph_sig.get_backward_star(n))) for n
        #              in self.subgraph_sig.node_iterator() if n[0] != '(' and n[0] != '<' and n not in preserve_nodes]
        # # sorted nodes_set by the number of forward and backward edges
        # nodes_set.sort(key=lambda x: x[1], reverse=False)
        # print("to be forget:", nodes_set)
        # for n, deg_n in tqdm(nodes_set):
        #     self.subgraph_sig.forget(n, delete_type)
        self.subgraph_sig.forget(preserve_nodes, delete_type)

        for left_id in self.subgraph_sig.hyperedge_id_iterator():
            print(left_id, self.subgraph_sig.get_hyperedge_attributes(left_id))

        return
