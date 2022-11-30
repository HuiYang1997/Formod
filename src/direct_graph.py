from halp.directed_hypergraph import DirectedHypergraph
from queue import Queue
from src.cluster import cluster
from itertools import product
from src.hyper_paths import hyperpaths


class Direct_graph(DirectedHypergraph):
    def __init__(self):
        super().__init__()

        # set of hyperedges_id in the subgraph extract by signature
        self.subgraph_sig = DirectedHypergraph()
        self.cluster = cluster()
        self.subgraph_sig_id_set = set()

        self.subgraph_sig_h_id2r_and_H_id = {}  # sub_h_id : {r: {h_id, ..., },...}

        # record "node_next--> node" for tracing backward phase
        self.nn = {}
        # can be viewed as "node--> node_next"
        self.subsumptions = {}

        # nodes (not in sig_c) that should consider as the start of a cluster
        self.node_start = set()

        self.sig_c = set()
        self.sig_r = set()

    def clear(self):
        self.subgraph_sig = DirectedHypergraph()
        self.cluster = cluster()
        self.subgraph_sig_id_set = set()

        self.subgraph_sig_h_id2r_and_H_id = {}

        self.nn = {}

        self.node_start = set()

    def add_edge(self, head, tail, attribute={}, f_sub=False):  # attributes : role --> axioms_id
        assert len(head) == len(tail) == 1  # here is actually a direct-graph
        if f_sub:
            try:
                h_id = self.get_hyperedge_id(tail, head)
                new_attribute = {**self.get_hyperedge_attributes(h_id), **attribute}
                self.subgraph_sig.add_hyperedge(head, tail, new_attribute)
            except ValueError:
                self.subgraph_sig.add_hyperedge(head, tail, attribute)

            # sub_h_id = self.subgraph_sig.get_hyperedge_id(head, tail)
            # self.subgraph_sig_id_set.add(sub_h_id)
            # self.subgraph_sig_h_id2r_and_H_id[sub_h_id] = {'': set()}
        else:
            try:
                h_id = self.get_hyperedge_id(tail, head)
                new_attribute = {**self.get_hyperedge_attributes(h_id), **attribute}
                self.add_hyperedge(head, tail, new_attribute)
            except ValueError:
                self.add_hyperedge(head, tail, attribute)

        return

    def get_forward_edges(self, node, flag_sub=False):
        if not flag_sub and self.has_node(node):
            yield node, iter(self.get_forward_star(node))
        elif flag_sub and self.subgraph_sig.has_node(node):
            yield node, iter(self.subgraph_sig.get_forward_star(node))

        if node in self.subsumptions:
            for node_next in self.subsumptions[node]:
                assert node_next != node
                if not flag_sub and self.has_node(node_next):
                    if node_next in self.nn:
                        self.nn[node_next].add(node)
                    else:
                        self.nn[node_next] = {node}

                    if node_next not in self.sig_c:  # here we do not trace forward beyond nodes in signature
                        yield node_next, iter(self.get_forward_star(node_next))
                elif flag_sub and self.subgraph_sig.has_node(node_next):
                    yield node_next, iter(self.subgraph_sig.get_forward_star(node_next))

    def renew_subgraph_sig(self, tail, new_head, original_id):
        # remember here new_id is id in H (not subgraph_sig)
        try:
            self.subgraph_sig.get_hyperedge_id(tail, new_head)
        except ValueError:
            self.subgraph_sig.add_hyperedge(tail, new_head, {})

        hyperedges_id = self.subgraph_sig.get_hyperedge_id(tail, new_head)
        attributes = self.get_hyperedge_attributes(original_id)
        new_attributes = {k: {original_id} for k in attributes if k in self.sig_r}

        if hyperedges_id in self.subgraph_sig_h_id2r_and_H_id:
            for k in new_attributes:
                if k in self.subgraph_sig_h_id2r_and_H_id[hyperedges_id]:
                    self.subgraph_sig_h_id2r_and_H_id[hyperedges_id][k].update(new_attributes[k])
                else:
                    self.subgraph_sig_h_id2r_and_H_id[hyperedges_id][k] = new_attributes[k]
        else:
            self.subgraph_sig_h_id2r_and_H_id[hyperedges_id] = new_attributes
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
                if (current_node, node_next) in visited_nodes:
                    continue

                for hyperedge_id in forward_star_iter:
                    if (current_node, hyperedge_id) in Pe:
                        continue
                    else:
                        attributes = self.get_hyperedge_attributes(hyperedge_id)
                        new_attributes = {k: attributes[k] for k in attributes if k in self.sig_r}
                        if new_attributes:
                            head_node_set = attributes['head']
                            union_start.add(current_node)
                            Pe.add((current_node, hyperedge_id))

                            self.node_start.update(head_node_set)

                            self.renew_subgraph_sig({current_node}, head_node_set, hyperedge_id)

                            # Traversing a hyperedge in current_node's forward star yields
                            # the set of head nodes of the hyperedge; visit each head node
                            for head_node in head_node_set:
                                if head_node not in self.sig_c and flag_add:
                                    self.node_start.add(head_node)
                                if head_node not in visited_nodes and head_node != current_node:
                                    Q.put(head_node)

                visited_nodes.add((current_node, node_next))
            visited_nodes.add(current_node)

        self.node_start.update(self.sig_c)
        return union_start

    def get_backward_edges(self, node, flag_sub=False):
        if not flag_sub and self.has_node(node):
            yield node, iter(self.get_backward_star(node))
        elif flag_sub and self.subgraph_sig.has_node(node):
            yield node, iter(self.subgraph_sig.get_backward_star(node))

        if node in self.nn:
            for node_pre in self.nn[node]:
                assert node_pre != node
                if not flag_sub and self.has_node(node_pre):
                    yield node_pre, iter(self.get_backward_star(node_pre))
                elif flag_sub and self.subgraph_sig.has_node(node_pre):
                    yield node_pre, iter(self.subgraph_sig.get_backward_star(node_pre))

    def traverse_backward(self, source_node_set):
        visited_node_set = set()
        for source_node in source_node_set:
            visited_node_set.update(self.traverse_backward_one_node(source_node))

        return visited_node_set

    def traverse_backward_one_node(self, source_node):
        # Explicitly tracks the set of visited nodes
        visited_nodes = set()

        Q = Queue()
        Q.put(source_node)

        while not Q.empty():
            current_node = Q.get()
            # At current_node, we can traverse each hyperedge in its forward star
            for node_pre, backward_star_iter in self.get_backward_edges(current_node, True):
                if node_pre in visited_nodes:
                    continue
                for sub_hyperedge_id in backward_star_iter:
                    # Traversing a hyperedge in current_node's forward star yields
                    # the set of head nodes of the hyperedge; visit each head node
                    tail_node_set = self.get_hyperedge_tail(sub_hyperedge_id)
                    self.subgraph_sig_id_set.add(sub_hyperedge_id)
                    if current_node not in tail_node_set or len(tail_node_set) == 1:
                        for tail_node in tail_node_set:
                            if tail_node not in visited_nodes and tail_node != current_node:
                                Q.put(tail_node)

                visited_nodes.add(node_pre)
            visited_nodes.add(current_node)

        return visited_nodes

    def build_cluster(self, source_node_set):
        self.cluster.sig_c = self.sig_c
        for sub_h_id in self.subgraph_sig.get_hyperedge_id_set():
            attribute = self.subgraph_sig.get_hyperedge_attributes(sub_h_id)
            tail = list(attribute['tail'])[0]
            head = list(attribute['head'])[0]
            assert self.subgraph_sig.has_node(tail)
            assert self.subgraph_sig.has_node(head)

            for r in self.subgraph_sig_h_id2r_and_H_id[sub_h_id]:
                self.cluster.add(tail, r, head)

            if head in self.subsumptions:
                for n_sig in self.subsumptions[head] & self.sig_c:
                    assert n_sig != head
                    self.cluster.add(head, "", n_sig)

        for n in self.sig_c:
            if n in self.subsumptions:
                for n_sig in self.subsumptions[n] & self.sig_c:
                    assert n_sig != n
                    self.cluster.add(n, "", n_sig)

        print(len(self.cluster.A2L))
        self.cluster.main(source_node_set)
        return
