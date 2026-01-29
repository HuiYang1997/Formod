# from src.preprocessing_terminology import initializing
# %%
from halp.directed_hypergraph import DirectedHypergraph
from pakages.resolution.tools import renew
from src.ontology import Ontology
from src.tools import split_two_part, unfold, mkdir, trans_back, trans, replace_el_plus_role_pattern
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
from src.extract_el_plus_edges import extract_EL_Plus_edges as extract_EL_Plus_edges_func
from src.extract_el_plus_edges import RoleChainLoopError

import copy
import time
import os
from func_timeout import FunctionTimedOut, func_set_timeout
from src.greedy_OneModule import greedy_search

from pprint import pp, pprint
from collections import defaultdict


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
    def __init__(self, name_ontology, path, sig_path='sig', count_c=None, k_E_role=None, el_plus_mode=False):
        trace_inference.__init__(self, path, name_ontology, count_c, k_E_role)

        # basic value
        self.name_ontology = name_ontology
        self.path = path
        self.ontology = None
        self.current_file = None
        self.sig_path = path + sig_path
        self.query_path = path + "query_" + sig_path
        
        # EL+ mode flag - when True, enables EL+ specific processing for role chains
        self.el_plus_mode = el_plus_mode
        mkdir(self.query_path)

        self.time_limit = 120

        self.concept_appear_count = {}

        # classification result
        self.subsumptions_direct = {}
        self.subsumptions = {}

        # hyper-graph and digraphj
        self.G = Direct_graph() # graph for forward trees
        self.G_loop_nodes = set([])
        self.H = Direct_hyper_graph() # hyper-graph for backward trees
        self.ont_H = Hypergraph_ont() # hyper-graph for forward and backward trees

        # signature
        self.sig_r = None
        self.sig_c = None

        self.subH_id = {}

        self.nonempty_queries = []

        self.owl2ind, self.a_ind = defaultdict(list), 3
        self.valid_ht = set()

        self.clauses = {'1': set()}  # assume 'final_goal' has index '1', loops part has index '2'
        self.answer_literals = set()

        self.s_t = None
        self.time_out_flag = False
        self.middle_nodes = set()

        self.infered_role_chains = set([])

    def clear(self):
        self.clear_trace_data()
        self.H.clear()
        self.G.clear()
        self.G_loop_nodes = set([])
        self.ont_H.avaliable_edges = set([])

        self.subH_id = {}

        self.nonempty_queries = []

        self.owl2ind, self.a_ind = defaultdict(list), 3
        self.valid_ht = set()

        self.clauses = {'1': set()}  # assume 'final_goal' has index '1', loops part has index '2'
        self.answer_literals = set()

        self.s_t = None
        self.time_out_flag = False
        self.middle_nodes = set()

        self.infered_role_chains = set([])    

    def initialize(self, start=True, max_chain_length=None):
        self.ontology = Ontology(self.name_ontology + '.owl', self.path, True, ind_form=False)
        self.initialize_indexed_and_hyper_edges()
        self.initialize_direct_subsumption(start)
        print("initial hyper-graph and digraph loaded!")

        # print("===============G.get_hyperedge_id_set() 1================")
        # for id in self.G.get_hyperedge_id_set():
        #     print(id, self.G.get_hyperedge_attributes(id))
        # print("=======================================================")

        for n in self.ontology.concepts:
            if not self.ont_H.has_node(n):
                print('nodes not in ont_H, ', n)

        for n in self.ontology.relations:
            if not self.ont_H.has_node(n):
                print('relations not in ont_H, ', n)

        if self.el_plus_mode:
            # Do not apply the optimizations based on terminology concepts for EL+ mode
            self.H.concept_non_terminology = {n for n in self.concept_appear_count}
        else:
            self.H.concept_non_terminology = {n for n in self.concept_appear_count if self.concept_appear_count[n] > 1}
            print("non terminology concept:", len(self.H.concept_non_terminology))
        
        # Initialize EL+ extension only if el_plus_mode is enabled
        # Role axiom check is done inside initialize_el_plus during data loading
        if self.el_plus_mode:
            self.initialize_el_plus(max_chain_length=max_chain_length)
        
        # print("===============G.get_hyperedge_id_set() 2================")
        # for id in self.G.get_hyperedge_id_set():
        #     print(id, self.G.get_hyperedge_attributes(id))
        # print("=======================================================")    

    def generate_signature(self, type='', num_concept=3, num_role=3, num_signature=2):
        concept_list_test = [num_concept] * num_signature  # generate num_signature signatures
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
        
        # in the EL+ case, extend the sig_r to include following roles of the form
        # 1. -r1-r2...-rn+t, where ri and t are in sig_r, and [r1, r2, ..., rn, t] is a reduced_chain finded when computing the path for EL+ case
        # 2. -r1-r2...-rn, where ri are in sig_r, and [r1, r2, ..., rn] is a reduced_chain finded when computing the extended path for EL+ case
        # note that ri above could be empty, the empty string is in sig_r
        if self.el_plus_mode and hasattr(self, 'el_plus_path_data'):
            extended_roles = set()
            for ind_path, _ in self.el_plus_path_data.items():
                attr_key = ind_path.split(' ')[1]
                roles_in_attr_key = attr_key.replace('+', '-').split('-')[1:] # ignore the first empty item ""
                print(attr_key, roles_in_attr_key, self.sig_r)
                if roles_in_attr_key and set(roles_in_attr_key).issubset(self.sig_r):
                    extended_roles.add(attr_key)
            # Extend sig_r with the new roles
            self.sig_r = frozenset(self.sig_r | extended_roles)
        
        print(f'#########signature_r extended:{self.sig_r}')

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

        print("===============G.get_hyperedge_id_set()================")
        for id in self.G.get_hyperedge_id_set():
            print(id, self.G.get_hyperedge_attributes(id))
        valid_nodes = self.G.traverse_forward(self.H.node_start | self.sig_c)
        print(valid_nodes, len(self.G.subgraph_sig.get_hyperedge_id_set()))
        print("===============G.subgraph_sig================")
        for id in self.G.subgraph_sig.get_hyperedge_id_set():
            print(id, self.G.subgraph_sig.get_hyperedge_attributes(id))

        for n in valid_nodes & self.H.node_start:
            if n in self.concept_appear_count and self.concept_appear_count[n] > 1 and n not in self.sig_c:
                self.middle_nodes.add(n)

        print("middle_nodes:", self.middle_nodes)
        print("H start, G start:", len(self.H.node_start), len(self.G.node_start))
        self.H.traverse_backward(self.middle_nodes | self.sig_c, valid_edges_H)
        # self.H.traverse_backward(self.sig_c, valid_edges_H)
        print("after(H):", len(self.H.subgraph_sig.get_hyperedge_id_set()))
        print("===========H subgraph_sig===========")
        for id in self.H.subgraph_sig.get_hyperedge_id_set():
            print(id, self.H.subgraph_sig.get_hyperedge_attributes(id))

    def initialize_el_plus(self, max_chain_length=None):
        """
        Initialize EL+ extension by computing paths from role chains and extending G and H.
        
        This method:
        1. Detects role inclusion/chain axioms
        2. Computes paths using extract_el_plus_edges
        3. Extends self.G with paths: {first_node} -> {last_node} with chain attributes
        4. Extends self.H with aggregated paths
        
        Parameters
        ----------
        max_chain_length : int
            Maximum length of role chains to consider.
        
        Raises
        ------
        RoleChainLoopError
            If the role axioms contain cycles (loops).
        """
        print("=== Initializing EL+ extension ===")
        
        print("***************axioms*************************")
        pprint(self.ontology.axioms)
        print("*******************RI*************")
        pprint(self.ontology.axioms_RI) 
        print("*******************RC*************")
        pprint(self.ontology.axioms_RC)  
        
        # Build role axiom dictionaries from self.ontology.axioms_RI and axioms_RC
        # These dictionaries map tuples to axiom strings for use in extract_EL_Plus_edges
        self.role_inclusion_axioms = {}  # (r1, r2) -> "SubObjectPropertyOf(<r1> <r2>)"
        self.role_chain_axioms = {}      # (t, r, s) -> "SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>)"
        self.role_tuple_to_str = {}      # Combined mapping for trace_inference compatibility

        self.role_axiom_str2id = copy.deepcopy(self.ontology.axioms_RI)
        self.role_axiom_str2id.update(self.ontology.axioms_RC)
        
        # Process role inclusion axioms from self.ontology.axioms_RI
        # Format: "SubObjectPropertyOf(<role1> <role2>)" -> axiom_id
        for axiom_str, axiom_id in self.ontology.axioms_RI.items():
            # Extract role names from axiom string
            # Format: SubObjectPropertyOf(<role1> <role2>)
            parts = axiom_str.replace("SubObjectPropertyOf(", "").replace(")", "").split("<")
            if len(parts) >= 3:
                r1 = parts[1].split(">")[0]
                r2 = parts[2].split(">")[0]
                self.role_inclusion_axioms[(r1, r2)] = axiom_str
                self.role_tuple_to_str[(r1, r2)] = axiom_str
        
        # Process role chain axioms from self.ontology.axioms_RC
        # Format: "SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>)" -> axiom_id
        for axiom_str, axiom_id in self.ontology.axioms_RC.items():
            # Extract role names from axiom string
            # Format: SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>)
            if 'ObjectPropertyChain' in axiom_str:
                # Extract roles from the chain
                parts = axiom_str.split('<')
                if len(parts) >= 4:
                    r = parts[1].split('>')[0]  # First role in chain
                    s = parts[2].split('>')[0]  # Second role in chain
                    t = parts[3].split('>')[0]  # Target role
                    self.role_chain_axioms[(t, r, s)] = axiom_str
                    self.role_tuple_to_str[(r, s, t)] = axiom_str
        
        print(f"Built {len(self.role_inclusion_axioms)} role inclusion axioms and {len(self.role_chain_axioms)} role chain axioms from ontology")
        
        # Initialize path index counter and storage for CNF generation
        self.el_plus_path_index = 0  # Counter for unique path IDs
        self.el_plus_path_data = {}  # {ind_path: {axioms: set, subsumptions: set, role_axiom_ids: set}}
        
        # Extract EL+ edges and role chains
        # Loop detection runs automatically and raises RoleChainLoopError if loop found
        try:
            result = extract_EL_Plus_edges_func(
                role_inclusion_axioms=self.role_inclusion_axioms,
                role_chain_axioms=self.role_chain_axioms,
                G=self.G,
                H=self.H,
                ont_H=self.ont_H,
                subsumptions=self.subsumptions,
                max_length=max_chain_length,
            )
        except RoleChainLoopError as e:
            raise RoleChainLoopError(
                f"Cannot process EL+ ontology: {e}"
            )
        
        # Store results
        self.el_plus_chains = result['all_chains']
        self.el_plus_paths_G = result['paths_G']
        self.el_plus_paths_H = result['paths_H']
        
        
        print("+++++++++++++el_plus_chains:++++++++++++++++ ")
        pprint(self.el_plus_chains)
        print("+++++++++++++el_plus_paths_G:++++++++++++++++ ")
        pprint(self.el_plus_paths_G)
        print("+++++++++++++el_plus_paths_H:++++++++++++++++ ")
        pprint(self.el_plus_paths_H)
        
        print(f"Found {len(result['all_chains'])} chains")
        print(f"Computed {len(self.el_plus_paths_G)} paths in G, {len(self.el_plus_paths_H)} aggregated paths with H")
        
        # Extend G with paths
        self._extend_G_with_paths(self.el_plus_paths_G)
        
        # Extend H with aggregated paths
        self._extend_H_with_paths(self.el_plus_paths_H)
        
        print(f"Created {len(self.el_plus_path_data)} indexed paths for CNF generation")
        print("=== EL+ initialization complete ===")
        return 

    def _extend_G_with_paths(self, paths):
        """
        Extend self.G edges with computed paths.
        
        For each path, add edge: {first_node} -> {last_node} with attribute:
        - "-r1-r2-...-rn+t": ind_path  (where [r1,...,rn,t] is the reduced chain with role names)
        
        Path index format: "{first_node} {attr_key} {last_node}"
        Multiple paths with the same index are stored as a list in self.el_plus_path_data.
        
        Each path data contains:
        - axioms: set of G edge axiom IDs (only for the specific role used)
        - subsumptions: set of (A, B) subsumption pairs
        - chain_axioms: list of role chain axioms used
        """
        extended_count = 0
        for path in paths:
            first_node = path.get("first_concept")
            last_node = path.get("last_concept")
            if first_node is None or last_node is None:
                continue
            
            # Get reduced chain - now uses original role names directly (no conversion needed)
            reduced_chain = path["reduced_chain"]
            assert len(reduced_chain) > 0, "reduced_chain should not be empty"
            
            # Chains now use original role names, just convert to strings for attr_key
            chain_with_names = [str(role) for role in reduced_chain]
            
            # Create attribute key: -r1-r2-...-rn+t format
            # The last role is the target role (t), others are chain roles
            assert len(chain_with_names) > 0
            if len(chain_with_names)>1:
                attr_key = f"-{'-'.join(chain_with_names[:-1])}+{chain_with_names[-1]}"
            else:
                attr_key = f"+{chain_with_names[-1]}"
            
            # Create path index: "{first_node} {attr_key} {last_node}"
            ind_path = f"{first_node} {attr_key} {last_node}"
            
            # Collect axioms from G edges - role names are used directly
            g_edges = path.get("edges", [])
            axiom_ids = set()
            for edge_tuple in g_edges:
                # edge_tuple is (A, role_name, B, edge_id) - role_name is now original name
                assert len(edge_tuple) == 4, f"edge_tuple should have 4 elements, got {len(edge_tuple)}"
                A, role_name, B, edge_id = edge_tuple
                # Get axiom ID for the specific role used in this edge
                attrs = self.G.get_hyperedge_attributes(edge_id)
                if role_name in attrs:
                    axiom_ids.add(attrs[role_name])
            
            # Collect subsumptions
            subsumptions = set()
            for sub in path.get("subsumptions", []):
                assert isinstance(sub, (list, tuple)) and len(sub) >= 2
                subsumptions.add((sub[0], sub[1]))

            
            # Store path data for CNF generation (as list since multiple paths can have same index)
            path_data = {
                'axioms': axiom_ids,
                'subsumptions': subsumptions,
                'chain_axioms': path['chain_axioms'],
                'type': 'G',
                'first': first_node,
                'last': last_node,
                'reduced_chain': reduced_chain,
                'chain': path['original_chain'],
            }
            
            if ind_path not in self.el_plus_path_data:
                self.el_plus_path_data[ind_path] = []
            self.el_plus_path_data[ind_path].append(path_data)
            
            # Add edge to G's subgraph_sig with the new attribute format
            self.G.add_hyperedge({first_node}, {last_node}, {attr_key: ind_path})
            print(f"==================add edge {first_node} -> {last_node} with attribute {attr_key}: {ind_path} to G")
            extended_count += 1
        
        print(f"Extended G with {extended_count} EL+ path edges")

    def _extend_H_with_paths(self, paths):
        """
        Extend self.H edges with aggregated paths.
        
        For each aggregated path, add edge: {first_node} -> {last_node} with attribute:
        - "-r1-r2-...-rn": ind_path  (where [r1,...,rn] is the reduced chain with role names)
        
        Path index format: "{first_node} {attr_key} {last_node}"
        Multiple paths with the same index are stored as a list in self.el_plus_path_data.
        
        Note: In H paths, the last element of reduced_chain is None (the target role t is
        consumed by the H edge ∃t.B' ⊑ B''), so we skip None when building chain_with_names.
        
        Each path data contains:
        - axioms: set of G edge axiom IDs + H edge axiom IDs (only for specific roles used)
        - subsumptions: set of all (A, B) subsumption pairs
        - chain_axioms: list of role chain axioms used
        """
        extended_count = 0
        for path in paths:
            first_node = path.get("first_concept")
            last_node = path.get("last_concept")
            
            # Get reduced chain - now uses original role names directly (no conversion needed)
            # Note: last element is None after H extension (target role consumed)
            reduced_chain = path["reduced_chain"]
            assert reduced_chain, "reduced chain can not be empty!"

            chain_with_names = []
            for role in reduced_chain:
                chain_with_names.append(str(role))
            
            # Create attribute key: -r1-r2-...-rn format (no +t for H paths since t is consumed)
            if not chain_with_names:
                # ignore the case with empty chain, as it corresponding to a conclusion O\models A\sqsubseteq B
                continue
            
            attr_key = '-' + '-'.join(chain_with_names)
            
            # Create path index: "{first_node} {attr_key} {last_node}"
            ind_path = f"{first_node} {attr_key} {last_node}"
            
            # Collect axioms from G edges - role names are used directly
            g_edges = path.get("edges", [])
            axiom_ids = set()
            for edge_tuple in g_edges:
                # edge_tuple is (A, role_name, B, edge_id) - role_name is now original name
                assert len(edge_tuple) == 4, f"G edge_tuple should have 4 elements, got {len(edge_tuple)}"
                A, role_name, B, edge_id = edge_tuple
                # Get axiom ID for the specific role used in this edge
                attrs = self.G.get_hyperedge_attributes(edge_id)
                if role_name in attrs:
                    axiom_ids.add(attrs[role_name])
            
            # Collect axioms from H edges - role names are used directly
            h_edges = path.get("H_edges", [])
            for h_edge_tuple in h_edges:
                # h_edge_tuple is (B_prime, role_name, B_double_prime, h_edge_id)
                assert len(h_edge_tuple) == 4, f"H edge_tuple should have 4 elements, got {len(h_edge_tuple)}"
                B_prime, role_name, B_double_prime, h_edge_id = h_edge_tuple
                # Get axiom ID for the specific role used in this H edge
                attrs = self.H.get_hyperedge_attributes(h_edge_id)
                if role_name in attrs:
                    axiom_ids.add(attrs[role_name])
            
            # Collect all subsumptions (G + H)
            subsumptions = set()
            for sub in path.get("subsumptions", []):
                assert isinstance(sub, (list, tuple)) and len(sub) >= 2
                subsumptions.add((sub[0], sub[1]))
            for sub in path.get("H_subsumptions", []):
                assert isinstance(sub, (list, tuple)) and len(sub) >= 2
                subsumptions.add((sub[0], sub[1]))
            
            # Store path data for CNF generation (as list since multiple paths can have same index)
            path_data = {
                'axioms': axiom_ids,
                'subsumptions': subsumptions,
                'chain_axioms': path['chain_axioms'],
                'type': 'H',
                'first': first_node,
                'last': last_node,
                'reduced_chain': reduced_chain,
                'chain': path['original_chain'],
            }
            
            if ind_path not in self.el_plus_path_data:
                self.el_plus_path_data[ind_path] = []
            self.el_plus_path_data[ind_path].append(path_data)
            
            # Add edge to H's subgraph_sig with the new attribute format
            self.H.add_hyperedge({first_node}, {last_node}, {attr_key: ind_path})
            extended_count += 1
            print(f"==================add edge {first_node} -> {last_node} with attribute '{attr_key}': {ind_path} to H")
        
        print(f"Extended H with {extended_count} EL+ path edges")

    def extract_EL_Plus_edges(self):
        """
        Extract EL+ edges based on role inclusion and role chain axioms.
        This function loads role axioms from data files and finds paths in G and H.
        
        DEPRECATED: Use initialize_el_plus() instead for full initialization.
        """
        datapath = self.path + 'data/'
        result = extract_EL_Plus_edges_func(
            datapath=datapath,
            G=self.G,
            H=self.H,
            ont_H=self.ont_H,
            subsumptions=self.subsumptions
        )
        
        # Store results for potential future use
        self.el_plus_chains = result['all_chains']
        self.el_plus_paths_G = result['paths_G']
        self.el_plus_paths_H = result['paths_H']
        
        return result

    def filter_redundancy_and_equivalence(self):
        owl_str = ''
        self.owl2ind, self.a_ind = defaultdict(list), 3  # assume 'final_goal' has index '1', loops part has index '2'
        # A\sqsubseteq B
        initilal_subsumption = {}
        for n in self.sig_c:
            if n in self.subsumptions:
                for n_super in self.subsumptions[n] & self.sig_c:
                    owl_str += trans_back(f'(implies <{n}> <{n_super}>)\n')
                    self.owl2ind[f'{n} {n_super}'].append(str(self.a_ind))
                    initilal_subsumption[str(self.a_ind)] = (n, n_super)
                    self.a_ind += 1
        
        # role axioms
        inferred_role_chain_in_sig_r = {}
        for chain_tuple in self.infered_role_chains:
            if len(chain_tuple) == 2:
                role_axiom_str = f"SubObjectPropertyOf(<{chain_tuple[0]}> <{chain_tuple[1]}>)"
            else:
                role_axiom_str = f"SubObjectPropertyOf(ObjectPropertyChain(<{"> <".join(chain_tuple[:-1])}>) <{chain_tuple[-1]}>)"
            owl_str += role_axiom_str + "\n"
            self.owl2ind[" ".join(chain_tuple)].append(str(self.a_ind))
            inferred_role_chain_in_sig_r[str(self.a_ind)] = chain_tuple
            self.a_ind += 1

        # C \sqsubseteq B, B in signature
        m2C = {}
        C_defined = {}
        ind2CD = {}
        print("===============subH_id===============")
        pprint(self.subH_id)
        for s_h_id in self.subH_id:
            head, C = self.subH_id[s_h_id]
            assert C[0] == '('

            # EL+ preprocessing: replace chain role patterns
            # if C contains substring of the form (some <-r1-r2...-rn> C1)
            # replace it by (some <r1> (some <r2> (... (some <rn> C1)...))), do it recursively.
            if self.el_plus_mode:
                C, _ = replace_el_plus_role_pattern(C)
         

            if C not in C_defined and C[0] == '(':
                owl_str += trans_back(f'(equivalent <N_{s_h_id}> {C})\n')
                C_defined[C] = f'N_{s_h_id}'

            if head in self.sig_c:
                owl_str += trans_back(f'(implies <{C_defined[C]}> <{head}>)\n')
                self.owl2ind[f'{C_defined[C]} {head}'].append(str(self.a_ind))
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
                                print(f"n: {n}, r: {r}, n_next: {n_next}, D: {D}")
                                if len(re.split('<|:', D)) <= 2:
                                    continue

                                # EL+ preprocessing: replace <+t> with <t> and chain role patterns
                                if self.el_plus_mode:
                                    D, place_holder = replace_el_plus_role_pattern(D)
                                
                                if D not in D_defined:
                                    if isinstance(n_next, str):
                                        n_next_str = n_next
                                    else:
                                        n_next_str = "-".join(n_next)
                                    owl_str += trans_back(f'(equivalent <M{n}_{r}_{n_next_str}> {D})\n')
                                    D_defined[D] = f'M{n}_{r}_{n_next_str}'
                                
                                if  self.el_plus_mode:
                                    if place_holder:
                                        print("place_holder:", place_holder)
                                        if n in self.sig_c:
                                            new_Con = f"N{n}_{r}_{n_next}" 
                                            owl_str += trans_back(f'(equivalent <{new_Con}> {place_holder.replace("X", f"<{n}>")})\n')
                                            owl_str += trans_back(f'(implies <{new_Con}> <{D_defined[D]}>)\n')
                                            self.owl2ind[f'{new_Con} {D_defined[D]}'].append(str(self.a_ind))
                                            ind2CD[str(self.a_ind)] = (n, None, (r, n_next))
                                            self.a_ind += 1
                                        else:
                                            # assert n in m2C
                                            if n in m2C:
                                                for N_C in m2C[n]:
                                                    new_Con = f"N{N_C}_{r}_{n_next}"
                                                    owl_str += trans_back(f'(equivalent <{new_Con}> {place_holder.replace("X", f"<{N_C}>")})\n')
                                                    owl_str += trans_back(f'(implies <{new_Con}> <{D_defined[D]}>)\n')
                                                    self.owl2ind[f'{new_Con} {D_defined[D]}'].append(str(self.a_ind))
                                                    ind2CD[str(self.a_ind)] = (n, N_C.split("_")[1], (r, n_next))
                                                    self.a_ind += 1
                                        continue
                                
                                if n in self.sig_c:
                                    owl_str += trans_back(f'(implies <{n}> <{D_defined[D]}>)\n')
                                    self.owl2ind[f'{n} {D_defined[D]}'].append(str(self.a_ind))
                                    ind2CD[str(self.a_ind)] = (n, None, (r, n_next))
                                    self.a_ind += 1
                                else:
                                    # assert n in m2C
                                    if n in m2C:
                                        for N_C in m2C[n]:
                                            owl_str += trans_back(f'(implies <{N_C}> <{D_defined[D]}>)\n')
                                            self.owl2ind[f'{N_C} {D_defined[D]}'].append(str(self.a_ind))
                                            ind2CD[str(self.a_ind)] = (n, N_C.split("_")[1], (r, n_next))
                                            self.a_ind += 1

        # # add an EL+-case
        # # if there is a path from {B}->{A} with reduced_chain [r1, r2, ...rn, t] with A a key in self.G.cluster.A2L and B in self.middle_nodes | self.sig_c:
        # # Create the following two axioms for D in self.G.cluster.transfer2C(A, r_res=r, k_res=n_next):
        # #  (equivalence <K> D)
        # #  (equivalence <K1> (some <r1>(some <r2>(... (some <rn> <head>)...))))
        # #  (implies <K1>  <K>)   
        # # and set self.owl2ind["K1 K"] = str(self.a_ind). 
        # # note that you should also call the cnf_encode function to encode the path here.
        # K_defined = {}
        # if self.el_plus_mode and hasattr(self, 'el_plus_path_data'):
        #     for ind_path, path_data_list in self.el_plus_path_data.items():
        #         for path_data in path_data_list:
        #             if path_data.get('type') != 'G':
        #                 continue  # Only process G paths here
                    
        #             first_node = path_data.get('first')  # B
        #             last_node = path_data.get('last')    # A
        #             reduced_chain = path_data.get('chain', [])
                    
        #             # Check if B is in middle_nodes | sig_c and A is in G.cluster.A2L
        #             if first_node not in (self.middle_nodes | self.sig_c):
        #                 continue
        #             if last_node not in self.G.cluster.A2L:
        #                 continue
                    
        #             # Extract chain role names from ind_path (already in name format)
        #             # ind_path format: "{first_node} {attr_key} {last_node}"
        #             # attr_key format: "-r1...-rn+t" for G paths
        #             parts = ind_path.split(' ')
        #             attr_key = parts[1]  # -r1-r2-...-rn+t
                    
        #             # Parse attr_key to get chain roles and target role
        #             # Format: -r1-r2-...-rn+t (chain roles before +, target after +)
        #             if '+' not in attr_key:
        #                 continue
        #             chain_part, _ = attr_key.rsplit('+', 1)
        #             chain_role_names = chain_part.split('-')[1:]  # Split and filter empty
        #             if not chain_role_names:
        #                 continue
                    
        #             # For all r in dic_A, build a big D as the conjunction of all D in dic_A[r] for all r
        #             dic_A = self.G.cluster.A2L.get(last_node, {})
                    
        #             # Collect all D concepts and D_tuples for all roles in dic_A
        #             all_D_concepts = []
        #             D_tuples = []
        #             for r in dic_A:
        #                 for n_next in dic_A[r]:
        #                     if r!="":
        #                         D_tuples.append((r, n_next))

        #                     for D in self.G.cluster.transfer2C(last_node, r_res=r, k_res=n_next):
        #                         if len(re.split('<|:', D)) <= 2:
        #                             continue
        #                         # Apply EL+ preprocessing to D
        #                         D = replace_el_plus_role_pattern(D)
        #                         all_D_concepts.append(D)
                    
        #             if not all_D_concepts:
        #                 continue
                    
        #             # Build big D as conjunction of all D concepts
        #             if len(all_D_concepts) == 1:
        #                 big_D = all_D_concepts[0]
        #             else:
        #                 big_D = '(and ' + ' '.join(all_D_concepts) + ')'
                    
        #             # Create K for big D if not already defined
        #             if big_D not in K_defined:
        #                 K_name = f'K_{last_node}'
        #                 owl_str += trans_back(f'(equivalent <{K_name}> {big_D})\n')
        #                 K_defined[big_D] = K_name
                    
        #             # Create K1 for (some <r1> (some <r2> (... (some <rn> <first_node>)...)))
        #             # Build nested some expression from inside out
        #             nested_expr = f'<{first_node}>'
        #             for role_name in reversed(chain_role_names):
        #                 nested_expr = f'(some <{role_name}> {nested_expr})'
                    
        #             K1_name = f'K1_{first_node}_{"_".join(chain_role_names) if chain_role_names else "empty"}'
        #             if nested_expr not in K_defined:
        #                 owl_str += trans_back(f'(equivalent <{K1_name}> {nested_expr})\n')
        #                 K_defined[nested_expr] = K1_name
        #             else:
        #                 K1_name = K_defined[nested_expr]
                    
        #             # Create (implies <K1> <K>)
        #             owl_str += trans_back(f'(implies <{K1_name}> <{K_defined[big_D]}>)\n')
        #             self.owl2ind[f'{K1_name} {K_defined[big_D]}'].append(str(self.a_ind))
        #             ind2CD[str(self.a_ind)] = (first_node, None, (ind_path, last_node, D_tuples))
        #             self.a_ind += 1

        print("==============ind2CD===========")
        pprint(owl_str)
        pprint(ind2CD)
        print("===============================")
        
        path_owl = self.path + 'filter_redundancy.owl'
        with open(path_owl, 'w') as f:
            f.write(f"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n{owl_str})\n")
            # f.write("Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n{}\n)\n".format('\n'.join(self.owl2ind.keys())))

        path_sub = self.path + 'filter_subsumption.txt'
        with open(path_sub, 'w') as f:
            f.write('\n'.join([k for k in self.owl2ind.keys() if len(k.split(" "))==2]) + '\n')

        # compute dominance
        path_result = self.path + 'filter_result.txt'
        command = f"java -jar pakages/numjust/numOfJust.jar {path_owl} {path_sub} {path_result} | grep '^[0-9]*$' | tail -n 1"
        os.system(command)
        # onto = ol.get_ontology(path_owl).load()
        # print(list(onto.classes()))

        # load dominance
        dic_dominant = DirectedHypergraph()
       
        equivalent_colletions = []
        for values in self.owl2ind.values():
            dic_dominant.add_nodes(values)
            if len(values) > 1:
                equivalent_colletions.append(set(values))


        redundant_ind = set()
        # filter equivalent nodes
        node_direct_subsumption = {}
        with open(path_result, 'r') as f:
            for line in f.readlines():
                li = re.sub(r"SubClassOf|SubObjectPropertyOf|ObjectPropertyChain|\(|\)|<|>", "", line).split(',')[:-1]
                # print(line, li)
                head = [self.owl2ind[li[0]][0]]
                for p in li[1:]:
                    tail = {self.owl2ind[a][0] for a in p.split("\t")[:-1] if a[0] != 'E'}

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
        
        print("==============dic_dominant===========")
        for id in dic_dominant.get_hyperedge_id_set():
            print(id, dic_dominant.get_hyperedge_attributes(id))
        print("===============================")


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
                elif n in node_direct_subsumption[k] and k in n_dominate_set and n!=k:
                    print("equivalent:" , n, k)
                    for s in equivalent_colletions:
                        if n in s or k in s:
                            s.add(n)
                            s.add(k)
                            break
                    else:
                        equivalent_colletions.append({n, k})

                    break

        print(redundant_ind)

        
        node2representative = {}
        for s in equivalent_colletions:
            list_s = list(s)
            for i in list_s[1:]:
                node2representative[i] = list_s[0]

        print("==============node2representative===========")
        pprint(node2representative)
        print("===============================")

        

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

        print("redundant_ind:", redundant_ind)

        # !!! make sure the index is unified
        self.count_id = self.a_ind

        # encode the derivation relations among all C->D
        for h_id in dic_dominant.get_hyperedge_id_set():
            tail = dic_dominant.get_hyperedge_tail(h_id)
            head_set = dic_dominant.get_hyperedge_head(h_id)

            new_head = {node2representative[h] if h in node2representative else h for h in head_set}
            new_tail = {node2representative[t] if t in node2representative else t for t in tail}
            print(h_id, head_set, tail)
            assert len(new_head) == 1
            if new_head != new_tail:
                for head in new_head:
                    assert head not in new_tail
                    if head in self.clauses:
                        self.clauses[head].append(new_tail)
                    else:
                        self.clauses[head] = [new_tail]

        print("==============clauses 1===========")
        pprint(self.clauses)
        print("===============================")

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
            
            if node in inferred_role_chain_in_sig_r:
                chain_tuple = inferred_role_chain_in_sig_r[node]
                id_chain = self.setid_rules2id(chain_tuple)
                self.clauses[node] = {id_chain}
    
            if node in ind2CD:
                A, e_id, D_tuple = ind2CD[node]
                pre_ids = []
                if e_id:
                    pre_ids.append(self.setid_rules2id(e_id))
                    self.valid_ht.add(e_id)
                if D_tuple:
                    # # Check if D_tuple is an EL+ path tuple (ind_path, target_role, n_next)
                    # if self.el_plus_mode and len(D_tuple) == 3:
                    #     ind_path, _, d_tuple = D_tuple
                    #     assert isinstance(ind_path, str) and hasattr(self, 'el_plus_path_data') and ind_path in self.el_plus_path_data
                    #     # EL+ case: add clause for C->B, B->A reduced chain [r1, r2, ...rn, t], and A->D
                    #     # => \exists r1 \exists r2 ... \exists rn C-> \exists t D
                    #     # path_clause_id, _ = self.build_cnf_el_plus_one(ind_path)
                    #     # if path_clause_id is not None:
                    #     #     pre_ids.append(path_clause_id)
                    #     # Also add the (A, (target_role, n_next)) tuple
                    #     pre_ids.append(self.setid_rules2id((A, d_tuple)))
                    #     self.valid_ht.add((A, d_tuple))
                    # else:
                    pre_ids.append(self.setid_rules2id((A, D_tuple)))
                    self.valid_ht.add((A, D_tuple))

                if node not in node2representative:
                    representative = node
                else:
                    representative = node2representative[node]
                
                if representative not in self.clauses:
                    self.clauses[representative] = [pre_ids]
                else:
                    self.clauses[representative].append(pre_ids)

        # '0' is the index of 'final_goal'
        self.clauses['1'].update({n for n in dic_dominant.node_iterator() if n not in node2representative})
        print("==============clauses 2===========")
        pprint(self.clauses)
        print("===============================")
        pprint(self.valid_ht)

     
        print("---------------self.owl2ind----------------")
        pprint(self.owl2ind)
        print("---------------ind2CD----------------")
        pprint(ind2CD)
        print("---------------self.rules2id----------------")
        pprint(self.rules2id)
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

            if id_history and r.startswith("-"):
                # ignore the case -r1...-rn+t appeared in the middle, 
                # not the first edge in the EL+ case.
                print(f"ignore {(A, r)}, id_history: {id_history}")
                continue

            for B in dic[r]:
                print(f"============== A: {A}, r: {r}, B: {B}")
                # avoid redundant cluster
                if A in self.sig_c | self.middle_nodes and (A, (r, B)) not in self.valid_ht:
                    print(f"ignore {(A, (r, B))}")
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
                        # EL+ case: if r starts with '-', it's an EL+ path
                        # The original_g_id is the ind_path (path index)
                        if self.el_plus_mode and r.startswith(('-', '+')):
                            # original_g_id is the ind_path for EL+ paths
                            ind_path = self.G.get_hyperedge_attribute(original_g_id, r)
                            # EL+ case: if r starts with '+', it's an EL+ path
                            path_clause_id, path_subs = self.build_cnf_el_plus_one(ind_path)
                            print(f"r(el+): {r}, ind_path: {ind_path}")
                            print("path_clause_id:", path_clause_id)
                            print("path_subs:", path_subs)
                            assert path_clause_id is not None
                            set_pre_B.add(path_clause_id)
                            subsumption_paris.update(path_subs)
                        else:
                            # Normal case: get axiom_id from edge attribute
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
        print('================ G.cluster.A2L================')
        pprint(self.G.cluster.A2L)
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
                        elif self.el_plus_mode and e in self.el_plus_path_data:
                            # EL+ case: e is an ind_path for an extended path
                            path_clause_id, path_subs = self.build_cnf_el_plus_one(e)
                            assert path_clause_id is not None
                            edges_id.add(path_clause_id)
                            subsumption_pairs.update(path_subs)
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

    def build_cnf_el_plus_one(self, ind_path):
        """
        Build CNF formula for a single EL+ path index.
        
        This method is called when meeting an extended path during build_cnf_t or build_cnf_h.
        
        Parameters
        ----------
        ind_path : str
            The path index in format "{first_node} {attr_key} {last_node}"
            
        Returns
        -------
        tuple
            (path_clause_id, subsumption_pairs) where path_clause_id is the encoded ID
            and subsumption_pairs is a set of (A, B) pairs from the path.
        """
        if not hasattr(self, 'el_plus_path_data') or ind_path not in self.el_plus_path_data:
            return None, set()
        
        subsumption_pairs = set()
        path_data_list = self.el_plus_path_data[ind_path]
        
        # Create clause ID for this path index - encode directly like axiom_id
        # Do NOT add to answer_literals since path_index is not an original axiom
        path_clause_id = self.setid_rules2id(ind_path)
        
        # Each path in the list creates a separate set of premises (disjunction)
        all_premise_sets = []
        
        for path_data in path_data_list:
            premise_ids = set()
            
            # Add axiom IDs from G/H edges to premises
            # These are original axioms, so add to answer_literals
            for axiom_id in path_data.get('axioms', set()):
                axiom_clause_id = self.setid_rules2id(axiom_id)
                premise_ids.add(axiom_clause_id)
                self.answer_literals.add(axiom_clause_id)
            
            # Add subsumption IDs to premises
            for sub_pair in path_data.get('subsumptions', set()):
                if len(sub_pair) >= 2:
                    A, B = sub_pair[0], sub_pair[1]
                    subsumption_pairs.add((A, B))
                    # Create subsumption ID using concept IDs
                    if A in self.concepts2id and B in self.concepts2id:
                        sub_id = self.setid_rules2id(
                            str(self.concepts2id[A]) + "\t" + str(self.concepts2id[B]))
                        premise_ids.add(sub_id)
            
            # add role chain ID
            role_chain_id = self.setid_rules2id(path_data['chain'])
            premise_ids.add(role_chain_id)
            
            # Build clause for the ind path
            all_premise_sets.append(premise_ids)    

            # Build Clause for role chain axioms
            chain_axioms = path_data["chain_axioms"]
            
            # Extract role axiom IDs from chain_axioms using role_axiom_str2id
            all_role_axioms = []
            if isinstance(chain_axioms, list) and len(chain_axioms) > 0:
                # Check if it's a list of lists (new structure) or a simple list (old structure)
                for axiom_set in chain_axioms:
                    role_axioms = []
                    for ax_text in axiom_set:
                        role_axiom_clause_id = self.setid_rules2id(self.role_axiom_str2id[ax_text])
                        self.answer_literals.add(role_axiom_clause_id)
                        role_axioms.append(role_axiom_clause_id)
                    all_role_axioms.append(role_axioms)

            # add clause for role chain axioms
            self.clauses[role_chain_id] = all_role_axioms

        # add clause for path
        self.clauses[path_clause_id] = all_premise_sets
        
        return path_clause_id, subsumption_pairs

    def build_cnf_el_plus(self):
        """
        Build CNF formulas for all EL+ paths.
        
        DEPRECATED: This method is kept for backward compatibility.
        EL+ path CNF is now built incrementally in build_cnf_t and build_cnf_h
        when meeting extended paths.
        
        Returns
        -------
        set
            Set of subsumption pairs (A, B) from all paths.
        """
        if not hasattr(self, 'el_plus_path_data') or not self.el_plus_path_data:
            return set()
        
        subsumption_pairs = set()
        total_paths = 0
        
        for ind_path in self.el_plus_path_data:
            _, subs = self.build_cnf_el_plus_one(ind_path)
            subsumption_pairs.update(subs)
            total_paths += len(self.el_plus_path_data[ind_path])
        
        print(f'Built CNF for {len(self.el_plus_path_data)} EL+ path indices ({total_paths} total paths)')
        return subsumption_pairs

    def build_cnf_role_chains(self):
        """
        Build CNF formulas for role chains based on sig_r.
        
        1. Extract non-looped role chains containing only roles in sig_r
        2. Group chains by chain tuple and collect all axiom sets
        3. Keep only minimal axiom sets (not a proper superset of another)
        4. Encode as CNF: {role_axiom_ids} -> {role_chain_id} for each axiom set
        5. Update clauses and extend key '1' with new role_chain_ids
        
        Parameters
        ----------
        sig_r : set
            Set of role names in the signature
            
        Returns
        -------
        set
            Set of new role_chain_ids added to clauses
        """
        if not hasattr(self, 'el_plus_chains') or not self.el_plus_chains:
            return set()
        
        # # Convert sig_r role names to role IDs used in chains
        # # Chains use IDs from role axiom files (1-based: r1=1, r2=2, etc.)
        # # ontology.relations uses different IDs (with 0,1 reserved for owl properties)
        # # We need to extract the role number from role names like "test#r1" -> 1
        # sig_r_chain_ids = set()
        # for r in sig_r:
        #     if isinstance(r, str):
        #         # Extract role number from names like "test#r1", "+test#r2", "-test#r1+test#r3"
        #         import re
        #         matches = re.findall(r'#r(\d+)', r)
        #         for m in matches:
        #             sig_r_chain_ids.add(int(m))
        
        # Step 1: Filter chains and group by chain tuple
        # Collect all axiom sets for each chain
        from collections import defaultdict
        chain_axiom_sets = defaultdict(list)  # chain_tuple -> list of axiom_id_sets
        
        for chain, all_axioms in self.el_plus_chains.items():
            # Skip chains with no axioms (single role chains)
            if not all_axioms:
                continue
            
            # Check if all roles in chain are in sig_r
            if not all(r in self.sig_r for r in chain):
                continue
            
            print("============role chains in sig_r!=========")
            print(chain, self.sig_r)    

            chain_tuple = tuple(chain)

            # Get role axiom IDs for this chain
            for axiom_set in all_axioms:
                role_axiom_ids = set()
                for ax_str in axiom_set:
                    if ax_str in self.role_axiom_str2id:
                        role_axiom_ids.add(self.role_axiom_str2id[ax_str])
            
                assert role_axiom_ids
                chain_axiom_sets[chain_tuple].append(frozenset(role_axiom_ids))
        
        if not chain_axiom_sets:
            return set()
        
        # Step 2: Filter redundant chains
        chain_target3premise = defaultdict(list)
        for chain_tuple in chain_axiom_sets:
            target = chain_tuple[-1]
            premise = list(chain_tuple)[:-1]
            chain_target3premise[target].append(premise)
        
        # Compute the recursive closure of chain_target3premise 
        # by recursively replacing one item n in a premise p1 with another premise p2 in chain_target3premise[n]
        # Record all new premises (chains) that are obtained by doing at least one replacement
        redundant_chain = set([])
        
        # For each target, compute all derivable premises through substitution
        for target, premises in chain_target3premise.items():
            closure_premises = set()
            
            # Start with original premises
            worklist = [tuple(p) for p in premises]
            seen = set(worklist)
            
            while worklist:
                current_premise = worklist.pop(0)
                
                # Try to expand current_premise by replacing each role with its derivations
                for i, role in enumerate(current_premise):
                    if role in chain_target3premise:
                        # Replace role at position i with each premise that derives it
                        for sub_premise in chain_target3premise[role]:
                            # Create new premise: current_premise[:i] + sub_premise + current_premise[i+1:]
                            new_premise = tuple(list(current_premise[:i]) + sub_premise + list(current_premise[i+1:]))
                            
                            if new_premise not in seen:
                                seen.add(new_premise)
                                worklist.append(new_premise)
                            
                            closure_premises.add(new_premise)
            
            if closure_premises:
                redundant_chain.add(tuple(list(closure_premises)+[target]))
        
        # Remove redundant chains: a chain is redundant if its premise can be derived from other chains
        minimal_entries = []
        for chain_tuple, ax_sets in chain_axiom_sets.items():
            if chain_tuple not in redundant_chain:
                for ax in ax_sets:
                    minimal_entries.append((chain_tuple, ax))
        
        print("===============================")
        print("redundant_chain :", redundant_chain)
        print("minimal_entries :", minimal_entries)

        
        # Step 3: Encode as CNF: {role_axiom_ids} -> {role_chain_id}
        # Create one clause for each axiom set
      
        for chain_tuple, ax_set in minimal_entries:
            # Create unique key for this role chain + axiom set combination
            role_chain_id = str(self.setid_rules2id(chain_tuple))
            
            # Build premise set from role axiom IDs
            premise_ids = set()
            for role_axiom_id in ax_set:
                role_axiom_clause_id = self.setid_rules2id(role_axiom_id)
                premise_ids.add(role_axiom_clause_id)
                # Add role axiom clause IDs to answer_literals
                self.answer_literals.add(role_axiom_clause_id)
            
            # Add clause: role_chain_id <- {role_axiom_ids}
            self.clauses[role_chain_id] = premise_ids
            self.infered_role_chains.add(chain_tuple)
    
        print(f'Built CNF for {len(minimal_entries)} minimal role chain axiom sets (from {len(chain_axiom_sets)} total)')

    def build_cnf(self, k, ):
        subsumption_paris = self.build_cnf_t()
        subsumption_paris.update(self.build_cnf_h())
        print('++++++++++++++self.answer_literals (before role chain part) ++++++++++')
        pprint(self.answer_literals)    
        
        # Build CNF for EL+ paths if in EL+ mode
        # if self.el_plus_mode:
        #     subsumption_paris.update(self.build_cnf_role_chains())
        
        print('num of subsumption pairs: ', len(subsumption_paris))

        # trace cnf formula for subsumptions
        result, s_a_pre, goal_id = self.trace_inference_rules(subsumption_paris)
        print('result: ', result)
        print('goal_id: ', goal_id)
        print('s_a_pre: ', s_a_pre)
        print('++++++++++++++self.clauses: ++++++++++')
        pprint(self.clauses)
        print('++++++++++++++self.answer_literals: ++++++++++')
        pprint(self.answer_literals)
        print('++++++++++++++self.rules2id: ++++++++++')
        pprint(self.rules2id)
        
        # Translate role axiom tuple-based IDs to our string-based IDs in EL+ mode
        # trace_inference_rules uses tuple keys:
        #   - (t1, t2) for role inclusions t1 ⊑ t2
        #   - (r, s, t) for role chains r ∘ s ⊑ t
        # We need to map these to our role_axiom_str2id IDs
        if self.el_plus_mode and hasattr(self, 'role_tuple_to_str'):
            id2rules = {v: k for k, v in self.rules2id.items()}
            
            def translate_role_axiom_id(clause_id):
                """Translate a role axiom tuple-based clause ID to our string-based ID."""
                if not isinstance(clause_id, (int, str)):
                    return clause_id
                cid = int(clause_id) if isinstance(clause_id, str) else clause_id
                if cid not in id2rules:
                    return clause_id
                key = id2rules[cid]
                # Check if this is a role axiom tuple
                if isinstance(key, tuple):
                    # Role inclusion: (t1, t2) - 2 string elements
                    # Role chain: (r, s, t) - 3 int elements
                    ax_str = self.role_tuple_to_str.get(key)
                    if ax_str and ax_str in self.role_axiom_str2id:
                        our_axiom_id = self.role_axiom_str2id[ax_str]
                        our_clause_id = self.setid_rules2id(our_axiom_id)
                        return int(our_clause_id) if isinstance(clause_id, int) else our_clause_id
                return clause_id
            
            # Translate s_a_pre
            translated_s_a_pre = set()
            for a in s_a_pre:
                translated_s_a_pre.add(translate_role_axiom_id(a))
            s_a_pre = translated_s_a_pre
            
            # Translate clause IDs in result (from trace_inference_rules)
            translated_result = {}
            for con_id, premises_list in result.items():
                new_con_id = translate_role_axiom_id(con_id)
                if isinstance(premises_list, set):
                    new_premises = {translate_role_axiom_id(p) for p in premises_list}
                    translated_result[new_con_id] = new_premises
                elif isinstance(premises_list, list):
                    new_premises_list = []
                    for premises in premises_list:
                        if isinstance(premises, (set, list)):
                            new_premises = [translate_role_axiom_id(p) for p in premises]
                            new_premises_list.append(new_premises)
                        else:
                            new_premises_list.append(translate_role_axiom_id(premises))
                    translated_result[new_con_id] = new_premises_list
                else:
                    translated_result[new_con_id] = premises_list
            result = translated_result
        
        self.clauses.update(result)

        s_a = {str(a) for a in s_a_pre}
        self.answer_literals.update(s_a)
        # add axiom id generated when extracting hyper-paths
        for a_id in self.H.axioms_id & self.rules2id.keys():
            if isinstance(a_id, str) and "-" in a_id:
                # ignore the id for reduced paths -r1-r2-...-rn in EL+ case
                continue
            a_clause_id = self.setid_rules2id(a_id)
            self.answer_literals.add(a_clause_id)

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
        with open(f'{query_file}/approximate_module.txt', 'w') as f_o:
            # f_o.write(f"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\nOntology(\n")
            if self.el_plus_mode:
                self.ontology.axioms.update(self.ontology.axioms_RI)
                self.ontology.axioms.update(self.ontology.axioms_RC)

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
            print("H subgraph sig attributes:", self.H.subgraph_sig.get_hyperedge_attributes(h_id))
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
                nodes_left.add(li[0])
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
        print("middle_nodes (before enumerate hyper-path on H):", self.middle_nodes)
        self.H.enumerate_hyper_paths(self.sig_c | self.middle_nodes)
        # self.H.enumerate_hyper_paths(self.sig_c, False)
        self.record_subH()

        # extract cluster
        print("middle_nodes:", self.middle_nodes)
        self.G.build_cluster(self.sig_c | self.middle_nodes)
        print('size clauses:', len(self.G.cluster.A2L))

        # Build CNF for role chains in EL+ mode
        if self.el_plus_mode:
            self.build_cnf_role_chains()
            
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


def test(path, name_ontology, count_c=None, k_E_role=None, type='', el_plus_mode=False):
    m = dominant_ini(name_ontology, path, count_c=count_c, k_E_role=k_E_role, el_plus_mode=el_plus_mode)
    m.initialize()

    if not os.path.exists(m.sig_path):
        m.generate_signature()
    else:
        print(f"signature already exists in {m.sig_path}")

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
    # name_ontology = argv[1]
    name_ontology = "ontology"
    count_c, k_E_role = None, None
    # Check for --el-plus flag in command line arguments
    el_plus_mode = '--el-plus' in argv
    time_out_list, all_time, m = test(path, name_ontology, count_c, k_E_role, '', el_plus_mode=el_plus_mode)
    print('all done in', time.time() - s_t)
