import copy

from halp.directed_hypergraph import DirectedHypergraph
from src.resolution_over_hypergraph import subH
from queue import Queue
import line_profiler
from tqdm import tqdm
import time, threading, multiprocessing


class Hypergraph_ont(DirectedHypergraph):
    def __init__(self):
        super().__init__()
        self.avaliable_edges = set([])
        self.source_nodes = set([])

    def traverse_forward(self):
        if not isinstance(self, DirectedHypergraph):
            raise TypeError("Algorithm only applicable to directed hypergraphs")

        # Pe consist of tracked hyperedges id
        Pe = set([])
        # Explicitly tracks the set of visited nodes
        visited_nodes = set([])

        # for n in source_nodes:
        #     self.nn[n] = {n}

        Q = Queue()
        for n in self.source_nodes:
            assert self.has_node(n)
            Q.put(n)

        # traverse all hyperedge and r-edge
        while not Q.empty():
            current_node = Q.get()
            visited_nodes.add(current_node)
            for hyperedge_id in self.get_forward_star(current_node):
                if self.avaliable_edges and hyperedge_id not in self.avaliable_edges:
                    continue
                if hyperedge_id in Pe:
                    continue
                else:
                    head_nodes = self.get_hyperedge_head(hyperedge_id)
                    tail_nodes = set(self.get_hyperedge_tail(hyperedge_id))
                    if tail_nodes.issubset(visited_nodes):
                        Pe.add(hyperedge_id)

                        # Traversing a hyperedge in current_node's forward star yields
                        # the set of head nodes of the hyperedge; visit each head node
                        for n in head_nodes:
                            if n not in visited_nodes:
                                Q.put(n)

        return Pe

    def traverse_backward(self):
        if not isinstance(self, DirectedHypergraph):
            raise TypeError("Algorithm only applicable to directed hypergraphs")

        # Pe consist of tracked hyperedges id
        Pe = set([])
        # Explicitly tracks the set of visited nodes
        visited_nodes = set([])

        # for n in source_nodes:
        #     self.nn[n] = {n}

        Q = Queue()
        for n in self.source_nodes:
            Q.put(n)

        # traverse all hyperedge and r-edge
        while not Q.empty():
            current_node = Q.get()
            visited_nodes.add(current_node)
            for hyperedge_id in self.get_backward_star(current_node):
                if self.avaliable_edges and hyperedge_id not in self.avaliable_edges:
                    continue
                if hyperedge_id in Pe:
                    continue
                else:
                    head_nodes = set(self.get_hyperedge_head(hyperedge_id))
                    tail_nodes = self.get_hyperedge_tail(hyperedge_id)
                    if head_nodes.issubset(visited_nodes):
                        Pe.add(hyperedge_id)

                        # Traversing a hyperedge in current_node's forward star yields
                        # the set of head nodes of the hyperedge; visit each head node
                        for n in tail_nodes:
                            if n not in visited_nodes:
                                Q.put(n)

        return Pe

    def traverse(self, signatures):
        # apply traverse_forward and traverse_backward recursively until the result do not change
        # return the set of hyperedges
        self.source_nodes = set(signatures)

        self.avaliable_edges = self.traverse_forward()

        i, len_ava_edges = 1, len(self.avaliable_edges)
        if len_ava_edges == 0:
            return set([]), set([])

        while True:
            if i % 2 == 0:
                self.avaliable_edges = self.traverse_forward()
            else:
                self.avaliable_edges = self.traverse_backward()

            i += 1
            l_new = len(self.avaliable_edges)
            if l_new == len_ava_edges or l_new == 0:
                break
            else:
                assert l_new < len_ava_edges
                len_ava_edges = l_new

        print("iteration:", i)

        H_ids, G_ids = set([]), set([])
        for e in self.avaliable_edges:
            try:
                h_id = self.get_hyperedge_attribute(e, 'r')
                H_ids.add(h_id)
            except ValueError:
                pass

            try:
                g_id = self.get_hyperedge_attribute(e, 'l')
                G_ids.add(g_id)
            except ValueError:
                pass

        return H_ids, G_ids
