"""
Module for extracting EL+ role chains and mapping them onto graph paths.

Key ideas
---------
1) Load role inclusion axioms and role chain axioms from disk.
2) Build all reachable role chains (with the axioms that justify them) while
   avoiding infinite recursion caused by repeated axioms.
3) Optionally project the discovered chains onto graphs `G` and `H` to find
   matching hyperedges.

Quick example (inline data)
---------------------------
>>> role_inclusions = {2: {3}}           # r2 ⊑ r3
>>> dic_tr_s = {(3, 1): {2}}             # r1 ∘ r2 ⊑ r3
>>> non_loop, loop = compute_role_chains(role_inclusions, dic_tr_s)
>>> len(non_loop) > 0
True
>>> result = extract_EL_Plus_edges(
...     datapath="/data",                # still needed to read files, but data is shown above
...     G=None, H=None, ont_H=None, subsumptions={}
... )
"""

import os
import pickle
import copy
import json
from collections import defaultdict
from pprint import pprint
from functools import lru_cache


def load_role_axioms(datapath, role_id_to_name=None):
    """
    Load role inclusion axioms and role chain axioms from disk.
    
    Role names are extracted directly from the axiom strings. The normalization
    process now preserves original role names (e.g., '#rr1', 'galen7.owl#hasRole')
    instead of converting them to integer IDs.

    Parameters
    ----------
    datapath : str
        Path to the data directory containing role_inclusion.txt and 
        dic_tr_s_original.pickle.
    role_id_to_name : dict or None
        Deprecated - no longer needed since original role names are preserved.

    Returns
    -------
    (role_inclusions, dic_tr_s, role_inclusion_axioms, role_chain_axioms)
    
    All keys use original role names (strings).
    """
    role_inclusions = defaultdict(set)
    role_inclusion_axioms = {}

    role_inclusion_file = os.path.join(datapath, "role_inclusion.txt")
    if os.path.exists(role_inclusion_file):
        with open(role_inclusion_file, "r") as f:
            for line in f:
                line = line.strip()
                if not line.startswith("SubObjectPropertyOf("):
                    continue
                parts = line.replace("SubObjectPropertyOf(", "").replace(")", "").split("<")
                if len(parts) < 3:
                    continue
                # Extract original role names directly (no longer #rN format)
                r1 = parts[1].split(">")[0]
                r2 = parts[2].split(">")[0]
                
                role_inclusions[r1].add(r2)
                role_inclusion_axioms[(r1, r2)] = line

    dic_tr_s_file = os.path.join(datapath, "dic_tr_s_original.pickle")
    dic_tr_s = {}
    role_chain_axioms = {}
    if os.path.exists(dic_tr_s_file):
        with open(dic_tr_s_file, "rb") as f:
            dic_tr_s = pickle.load(f)
        # dic_tr_s now contains original role names as keys/values
        # Build role_chain_axioms from the data
        for (t, r), s_set in dic_tr_s.items():
            for s in s_set:
                # Store axiom string with original role names
                role_chain_axioms[(t, r, s)] = (
                    f"SubObjectPropertyOf(ObjectPropertyChain(<{r}> <{s}>) <{t}>)"
                )

    return role_inclusions, dic_tr_s, role_inclusion_axioms, role_chain_axioms


class RoleChainLoopError(Exception):
    """Raised when role inclusion graph contains cycles and fail_on_loop=True."""
    pass


class _RoleChainBuilder:
    """
    Build role chains directly via recursive backward expansion.
    
    For r1 ⊑ r2: chain [r1, r2]
    For r ∘ s ⊑ t: chain [r, s, t]
    
    Algorithm: For each target role t, recursively expand backward:
    - If r ⊑ t, prepend chains ending at r
    - If r ∘ s ⊑ t, prepend chains ending at r and s (in order)
    
    The `visited` set tracks the path from root to current node, ensuring no
    duplicate roles appear on any root-to-leaf path in the expansion tree.
    """

    def __init__(self, role_inclusions, dic_tr_s, role_inclusion_axioms=None,
                 role_chain_axioms=None, roles=None):
        self.role_inclusions = role_inclusions or {}
        self.dic_tr_s = dic_tr_s or {}
        self.inc_axioms = role_inclusion_axioms or {}
        self.chain_axioms = role_chain_axioms or {}
        
        # Build reverse lookup: target -> [(source, axiom)] for inclusions
        #                       target -> [((r, s), axiom)] for chains
        self.inc_to = defaultdict(list)   # t -> [(r, axiom)] where r ⊑ t
        self.chain_to = defaultdict(list) # t -> [((r, s), axiom)] where r∘s ⊑ t
        self.has_outgoing = set()
        
        for r1, targets in self.role_inclusions.items():
            for r2 in targets:
                if r1 != r2:
                    ax = self.inc_axioms.get((r1, r2), f"SubObjectPropertyOf(<#r{r1}> <#r{r2}>)")
                    self.inc_to[r2].append((r1, ax))
                    self.has_outgoing.add(r1)
        
        for (t, r), s_set in self.dic_tr_s.items():
            for s in s_set:
                ax = self.chain_axioms.get((t, r, s),
                    f"SubObjectPropertyOf(ObjectPropertyChain(<#r{r}> <#r{s}>) <#r{t}>)")
                self.chain_to[t].append(((r, s), ax))
                self.has_outgoing.add(r)
                self.has_outgoing.add(s)
        
        # Collect all roles
        if roles:
            self.roles = set(roles)
        else:
            self.roles = set()
            for r1, targets in self.role_inclusions.items():
                self.roles.add(r1)
                self.roles.update(targets)
            for (t, r), s_set in self.dic_tr_s.items():
                self.roles.add(t)
                self.roles.add(r)
                self.roles.update(s_set)

    def detect_loops(self):
        """
        Detect loops in the role hierarchy.
        
        A loop is detected if there exists a path r1->r2->...->r1 where each edge
        corresponds to an axiom of the form:
        - ri ⊑ r{i+1} (role inclusion)
        - ri ∘ t ⊑ r{i+1} (role chain)
        - t ∘ ri ⊑ r{i+1} (role chain)
        
        Raises
        ------
        RoleChainLoopError
            If a loop is detected. The error message contains the loop path and axioms.
        """
        # Use DFS to detect cycles - raise error on first loop found
        def dfs(role, path, axioms, visited_in_path):
            if role in visited_in_path:
                # Found a cycle - raise error immediately
                cycle_start = path.index(role)
                loop_path = path[cycle_start:] + [role]
                loop_axioms = axioms[cycle_start:]
                raise RoleChainLoopError(
                    f"Loop detected in role hierarchy: {' -> '.join(str(r) for r in loop_path)}. "
                    f"Axioms: {loop_axioms}. "
                    f"Role chains with loops do not fit the requirement."
                )
            
            visited_in_path.add(role)
            
            # Follow role inclusions: role ⊑ target
            for target in self.role_inclusions.get(role, []):
                if role != target:
                    ax = self.inc_axioms.get((role, target), f"SubObjectPropertyOf(<#r{role}> <#r{target}>)")
                    dfs(target, path + [role], axioms + [ax], visited_in_path.copy())
            
            # Follow role chains where role appears on the left: role ∘ s ⊑ t
            for (t, r), s_set in self.dic_tr_s.items():
                if r == role:
                    for s in s_set:
                        ax = self.chain_axioms.get((t, r, s),
                            f"SubObjectPropertyOf(ObjectPropertyChain(<#r{r}> <#r{s}>) <#r{t}>)")
                        dfs(t, path + [role], axioms + [ax], visited_in_path.copy())
            
            # Follow role chains where role appears on the right: r ∘ role ⊑ t
            for (t, r), s_set in self.dic_tr_s.items():
                if role in s_set:
                    ax = self.chain_axioms.get((t, r, role),
                        f"SubObjectPropertyOf(ObjectPropertyChain(<#r{r}> <#r{role}>) <#r{t}>)")
                    dfs(t, path + [role], axioms + [ax], visited_in_path.copy())
        
        # Start DFS from each role
        for role in self.roles:
            dfs(role, [], [], set())
    
    def compute(self, max_length=None):
        """
        Compute all role chains.
        
        Parameters
        ----------
        max_length : int or None
            Maximum chain length. None means no limit.
        
        Returns (non_loop_chains, loop_chains) where each chain is:
        {"chain": [r1, ..., t], "axioms": [[...], [...], ...]}
        where axioms is a list of axiom sets, one for each derivation path.
        
        Raises
        ------
        RoleChainLoopError
            If a loop is detected in the role hierarchy.
        """
        if not self.roles:
            return [], []
        
        # Run loop detection first - raises error if loop found
        self.detect_loops()
        
        # Dictionary to store chain -> list of axiom sets
        chain_to_axiom_sets = defaultdict(list)
        
        # Start from all roles that have incoming edges (are targets of some axiom)
        targets = set(self.inc_to.keys()) | set(self.chain_to.keys())
        # print("targets", targets)
        # # Also include isolated roles
        # targets |= self.roles
        
        for target in targets:
            for chain, axioms in self._expand(target, max_length):
                key = tuple(chain)
                # Extend the list instead of ignoring duplicates
                chain_to_axiom_sets[key].append(axioms)

        return chain_to_axiom_sets



    # @lru_cache(maxsize=None)
    def _expand(self, target, max_len):
        """
        Recursively expand backward from target.
        
        The `visited` set ensures no role appears twice on the path from root
        to any leaf, preventing infinite recursion in cyclic graphs.
        
        Yields (chain, axioms) tuples.
        """
        # Check length limit (None means no limit)
        if max_len is not None and max_len < 1:
            return
        
        # # Loop detection: target already on current path
        # if target in visited:
        #     return
        
        next_len = None if max_len is None else max_len - 1
        

        # Expand via role inclusions: r ⊑ target
        for r, axiom in self.inc_to.get(target, []):
            yield [r, target], [axiom]
            
            for sub_chain, sub_ax in self._expand(r, next_len):
                yield sub_chain[:-1] + [target], sub_ax + [axiom]
            
        
        # Expand via role chains: r ∘ s ⊑ target
        for (r, s), axiom in self.chain_to.get(target, []):
            yield [r, s, target], [axiom]

            # Collect r_chain results
            r_results = list(self._expand(r, next_len))
            
            # Collect s_chain results  
            s_results = list(self._expand(s, next_len))
            
            # print("===================")
            # print("target", target)
            # print(r_results)
            # print(s_results)
            # print(r, s, max_len, next_len)
            # print("===================")
            
            # Case 1: Both have results
            if r_results and s_results:
                for r_chain, r_ax in r_results:
                    for s_chain, s_ax in s_results:
                        yield r_chain[:-1] + s_chain[:-1] + [target], r_ax + s_ax + [axiom]
            
            # Case 2: Only r has results, s is empty
            elif r_results and not s_results:
                for r_chain, r_ax in r_results:
                    yield r_chain[:-1] + [s, target], r_ax + [axiom]
            
            # Case 3: Only s has results, r is empty
            elif not r_results and s_results:
                for s_chain, s_ax in s_results:
                    #print("s_chain", s_chain)
                    yield [r] + s_chain[:-1] + [target], s_ax + [axiom]

         
        



# def compute_role_chains(
#     role_inclusions,
#     dic_tr_s,
#     role_inclusion_axioms=None,
#     role_chain_axioms=None,
#     roles=None,
#     max_length=None,
# ):
#     """
#     Convenience wrapper to build role chains without constructing graphs.

#     Parameters
#     ----------
#     max_length : int or None
#         Maximum chain length. None means no limit.

#     Inline example
#     --------------
#     >>> ri = {2: {3}}
#     >>> dic = {(3, 1): {2}}
#     >>> non_loop, loop = compute_role_chains(ri, dic)
#     >>> non_loop[0]["chain"]
#     [1, 2, 3]
#     """
#     builder = _RoleChainBuilder(
#         role_inclusions=role_inclusions,
#         dic_tr_s=dic_tr_s,
#         role_inclusion_axioms=role_inclusion_axioms,
#         role_chain_axioms=role_chain_axioms,
#         roles=roles,
#     )
#     return builder.compute(max_length=max_length)


class ELPlusEdgesExtractor:
    """Extractor for EL+ role chains and paths."""

    def __init__(
        self,
        role_inclusion_axioms=None,
        role_chain_axioms=None,
        G=None,
        H=None,
        subsumptions=None,
    ):
        """
        Parameters
        ----------
        role_inclusion_axioms : dict
            Dictionary mapping (r1, r2) tuples to axiom strings for role inclusions r1 ⊑ r2.
            Example: {('role1', 'role2'): 'SubObjectPropertyOf(<role1> <role2>)'}
        role_chain_axioms : dict
            Dictionary mapping (t, r, s) tuples to axiom strings for role chains r ∘ s ⊑ t.
            Example: {('t', 'r', 's'): 'SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>)'}
        G: Forward graph containing hyperedges of the from {A} -> {B} with attribute {'r':id_edge}, corresponding to axiom A\sqsubseteq \exists r. B
        H: Backward graph containing hyperedges of the from 
            1. {B} -> {A} with attribute {'l':id_edge}, corresponding to axiom \exists r. B\sqsubseteq  A
            2. {A1, ... An} -> {A} with attribute {'h':id_edge}, corresponding to axiom A1\sqcap...\sqcap An\sqsubseteq A
        subsumptions :   Concept subsumption map A -> {B, ...}. Representing O \models A \sqsubseteq B
        """
        self.G = G
        self.H = H
        self.subsumptions = subsumptions

        # Encode role axiom strings directly
        self.role_inclusion_axioms = role_inclusion_axioms or {}
        self.role_chain_axioms = role_chain_axioms or {}
        
        # Build role_inclusions from role_inclusion_axioms
        # role_inclusions: {r1: {r2, r3, ...}} meaning r1 ⊑ r2, r1 ⊑ r3, ...
        self.role_inclusions = defaultdict(set)
        for (r1, r2), axiom_str in self.role_inclusion_axioms.items():
            self.role_inclusions[r1].add(r2)
        
        # Build dic_tr_s from role_chain_axioms
        # dic_tr_s: {(t, r): {s1, s2, ...}} meaning r ∘ s1 ⊑ t, r ∘ s2 ⊑ t, ...
        self.dic_tr_s = defaultdict(set)
        for (t, r, s), axiom_str in self.role_chain_axioms.items():
            self.dic_tr_s[(t, r)].add(s)

        self.roles = self._infer_roles()
        self.concepts = self._infer_concepts()
        self._role_chain_builder = _RoleChainBuilder(
            self.role_inclusions,
            self.dic_tr_s,
            self.role_inclusion_axioms,
            self.role_chain_axioms,
            self.roles,
        )

    def _infer_roles(self):
        roles = set()
        for r1, targets in self.role_inclusions.items():
            roles.add(r1)
            roles.update(targets)
        for (t, r), s_set in self.dic_tr_s.items():
            roles.add(t)
            roles.add(r)
            roles.update(s_set)
        if self.G is not None and hasattr(self.G, "sig_r"):
            roles.update(self.G.sig_r)
        return roles

    def _infer_concepts(self):
        concepts = set()
        if self.subsumptions:
            for a, supers in self.subsumptions.items():
                concepts.add(a)
                concepts.update(supers)
        if self.G is not None and hasattr(self.G, "sig_c"):
            concepts.update(self.G.sig_c)
        return concepts

    def compute_paths(self, max_chain_length=None):
        """
        Compute ALL paths according to the given role chains.

        For each role chain [r_1, r_2, ..., r_n, t], find paths where for some k (1 <= k <= n):
        1. An axiom A_k ⊑ ∃r_k.B_k exists (indicated by edge in self.G)
        2. A subsumption B_k ⊑ A_{k+1} exists (indicated by self.subsumptions), or B_k = A_{k+1}

        Algorithm: Progressive search from k=n down to k=1.

        Returns
        -------
        list of dict
            Each dict contains:
            - "original_chain": the full role chain [r_1, ..., r_n, t]
            - "reduced_chain": [r_1, ..., r_{k-1}, t] (roles before the matched position)
            - "k": the position where the path starts
            - "edges": list of (A, r, B, edge_id) tuples from G
            - "subsumptions": list of (B_i, A_{i+1}) pairs used (excluding identity)
        """
        if self.G is None:
            return []

        # Compute all role chains
        all_chains = self._role_chain_builder.compute(max_length=max_chain_length)

        # print("+++++++++++++++")
        # print("all_chains")
        # pprint(all_chains)
        # print("+++++++++++++++")

        # Build index: role -> [(tail_node, head_node, edge_id)]
        role_edges = self._build_role_edge_index()

        results = []
        for chain, axioms in all_chains.items():
            # Skip single-role chains (no roles to process, just target)
            if len(chain) < 2:
                continue

            # chain = [r_1, r_2, ..., r_n, t] where t is the target role
            roles = list(chain[:-1])  # [r_1, ..., r_n]
            t = chain[-1]
            n = len(roles)

            # print("+++++++++++++++")
            # print("chain", chain)
            # print("roles", roles)
            # print("t", t)
            # print("n", n)

            # Progressive search from k=n down to k=1
            paths = self._find_paths_progressive(roles, t, n, role_edges)
            for path in paths:
                path["original_chain"] = chain
                path["chain_axioms"] = axioms
                results.append(path)

        return results

    def _build_role_edge_index(self):
        """Build index: role_name -> [(A, B, edge_id)] for edges A ⊑ ∃r.B in G.
        
        The index uses original role names as keys (matching the role names in chains).
        """
        role_edges = {}
        if self.G is None:
            return role_edges

        for edge_id in self.G.hyperedge_id_iterator():
            tail = self.G.get_hyperedge_tail(edge_id)  # {A}
            head = self.G.get_hyperedge_head(edge_id)  # {B}
            attrs = self.G.get_hyperedge_attributes(edge_id)
            
            for role_name, axiom_id in attrs.items():
                # Skip non-role attributes
                if role_name in ('head', 'tail', 'weight'):
                    continue
                
                # Use role name directly as key (chains now use original role names)
                if role_name not in role_edges:
                    role_edges[role_name] = []
                for a in tail:
                    for b in head:
                        role_edges[role_name].append((a, b, edge_id))

        return role_edges

    def _find_paths_progressive(self, roles, t, n, role_edges):
        """
        Find paths progressively from k=n down to k=1.

        Algorithm:
        - Start at k=n: paths are single edges A_n ⊑ ∃r_n.B_n
        - For k=n-1 down to 1: extend paths from k+1 by prepending edge for r_k
          with subsumption B_k ⊑ A_{k+1} (or B_k = A_{k+1})

        If r_k not in role_edges for any k, there are no valid paths for this chain.

        Returns list of path dicts, each with:
        - "edges": list of (A, r, B, edge_id)
        - "subsumptions": list of (B_i, A_{i+1}) pairs used
        - "reduced_chain": [r_1, ..., r_{k-1}, t]
        - "k": starting position
        """
        results = []

        # paths_at_k[k] = list of (first_concept, last_concept, edges, subsumptions)
        # first_concept is A_k, last_concept is B_n (from the last edge)
        paths_at_k = {}

        # Base case: k = n
        r_n = roles[n - 1]
        if r_n not in role_edges:
            return []

        paths_at_k[n] = []
        for A_n, B_n, edge_id in role_edges[r_n]:
            paths_at_k[n].append((A_n, B_n, [(A_n, r_n, B_n, edge_id)], []))

        # Record results for k=n
        for first_A, last_B, edges, subs in paths_at_k[n]:
            reduced_chain = roles[:n-1] + [t] if n > 1 else [t]
            results.append({
                "edges": edges,
                "subsumptions": subs,
                "reduced_chain": reduced_chain,
                "k": n,
                "first_concept": first_A,
                "last_concept": last_B,
            })

        # Progressive: k = n-1 down to 1
        for k in range(n - 1, 0, -1):
            r_k = roles[k - 1]
            paths_at_k[k] = []

            for A_k, B_k, edge_id in role_edges.get(r_k, []):
                # Try to extend each path from k+1
                for first_A_next, last_B_next, edges_next, subs_next in paths_at_k[k + 1]:
                    # Check if B_k connects to first_A_next
                    if B_k == first_A_next:
                        # Direct connection
                        new_edges = [(A_k, r_k, B_k, edge_id)] + edges_next
                        paths_at_k[k].append((A_k, last_B_next, new_edges, subs_next[:]))
                    elif self.subsumptions and B_k in self.subsumptions:
                        if first_A_next in self.subsumptions[B_k]:
                            # Subsumption B_k ⊑ first_A_next
                            new_edges = [(A_k, r_k, B_k, edge_id)] + edges_next
                            new_subs = [(B_k, first_A_next)] + subs_next
                            paths_at_k[k].append((A_k, last_B_next, new_edges, new_subs))

            # Record results for this k
            for first_A, last_B, edges, subs in paths_at_k[k]:
                reduced_chain = roles[:k-1] + [t] if k > 1 else [t]
                results.append({
                    "edges": edges,
                    "subsumptions": subs,
                    "reduced_chain": reduced_chain,
                    "k": k,
                    "first_concept": first_A,
                    "last_concept": last_B,
                })
        # print("finded paths")
        # pprint(results)
        return results

    def aggregate_paths_with_H(self, paths):
        """
        Aggregate paths by extending them using H graph.

        For each path with first_concept=A, last_concept=B, last_role=t:
        - If B ⊑ B' in subsumptions (or B = B') AND there's an edge ∃t.B' ⊑ B'' in H,
          create extended paths with updated last_concept=B''.

        Each path is checked once for all possible extensions. Paths that cannot
        be extended are ignored.

        Parameters
        ----------
        paths : list of dict
            Paths from compute_paths, each with first_concept, last_concept, etc.

        Returns
        -------
        list of dict
            Extended paths with additional H_edges and H_subsumptions recorded.
        """
        if self.H is None:
            return []

        # Build index for H: role -> [(B', B'', edge_id)]
        # H edges represent ∃t.B' ⊑ B''
        h_role_edges = {}
        for edge_id in self.H.hyperedge_id_iterator():
            tail = self.H.get_hyperedge_tail(edge_id)  # {B'}
            head = self.H.get_hyperedge_head(edge_id)  # {B''}
            attrs = self.H.get_hyperedge_attributes(edge_id)

            for role, axiom_id in attrs.items():
                # Skip non-role attributes
                if role in ('head', 'tail', 'weight'):
                    continue

                if role not in h_role_edges:
                    h_role_edges[role] = []
                for b_prime in tail:
                    for b_double_prime in head:
                        h_role_edges[role].append((b_prime, b_double_prime, edge_id))

        results = []
        for path in paths:
            # Get the target role t (last element of reduced_chain)
            reduced_chain = path.get("reduced_chain", [])
            if len(reduced_chain) <=1: 
                #ignore the case reduce chain is just one role: 
                # it will leads to a subsumptions O \modeles A\sqsubseteq B, 
                # not a specific conlusion we desired: O \modeles \exists r. ...\exists t. A\sqsubseteq B,
                continue
            t = reduced_chain[-1]

            if t not in h_role_edges:
                continue

            B = path["last_concept"]

            # Find all possible extensions for this path
            candidates = []

            # Direct: B is B' (no subsumption needed)
            for B_prime, B_double_prime, h_edge_id in h_role_edges[t]:
                if B == B_prime:
                    candidates.append((B_prime, B_double_prime, h_edge_id))
                # Via subsumption: B ⊑ B'
                elif self.subsumptions and B in self.subsumptions:
                    if B_prime in self.subsumptions[B]:
                        candidates.append((B_prime, B_double_prime, h_edge_id))

            # Create extended paths for each candidate
            for B_prime, B_double_prime, h_edge_id in candidates:
                new_path = copy.deepcopy(path)
                new_path["H_edges"] = [(B_prime, t, B_double_prime, h_edge_id)]
                if B_prime != B:
                    new_path["H_subsumptions"] = [(B, B_prime)]
                else:
                    new_path["H_subsumptions"] = []
                new_path["last_concept"] = B_double_prime
                new_path["reduced_chain"] = new_path["reduced_chain"][:-1]
                results.append(new_path)

        return results

    def detect_loops(self):
        """Detect loops in the role hierarchy using the internal builder.
        
        Raises
        ------
        RoleChainLoopError
            If a loop is detected.
        """
        self._role_chain_builder.detect_loops()
    
    def compute_role_chains(self, max_length=None):
        """Compute role chains using the internal builder.
        
        Parameters
        ----------
        max_length : int or None
            Maximum chain length. None means no limit.
        """
        return self._role_chain_builder.compute(max_length=max_length)


def extract_EL_Plus_edges(
    role_inclusion_axioms=None,
    role_chain_axioms=None,
    G=None,
    H=None,
    ont_H=None,
    subsumptions=None,
    max_length=10,
):
    """
    User-facing convenience wrapper.
    
    Parameters
    ----------
    role_inclusion_axioms : dict
        Dictionary mapping (r1, r2) tuples to axiom strings for role inclusions r1 ⊑ r2.
        Example: {('role1', 'role2'): 'SubObjectPropertyOf(<role1> <role2>)'}
    role_chain_axioms : dict
        Dictionary mapping (t, r, s) tuples to axiom strings for role chains r ∘ s ⊑ t.
        Example: {('t', 'r', 's'): 'SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>)'}
    G : graph or None
        Forward graph containing hyperedges
    H : graph or None
        Backward graph containing hyperedges
    ont_H : graph or None
        Ontology graph (currently unused)
    subsumptions : dict or None
        Concept subsumption map A -> {B, ...}
    max_length : int
        Maximum chain length
    
    Returns
    -------
    dict with keys:
        - "all_chains": dict of role chains (using original role names)
        - "paths_G": list of paths found in G graph
        - "paths_H": list of aggregated paths extended with H graph
    
    Raises
    ------
    RoleChainLoopError
        If a loop is detected in the role hierarchy during chain computation.
    """
    extractor = ELPlusEdgesExtractor(
        role_inclusion_axioms=role_inclusion_axioms,
        role_chain_axioms=role_chain_axioms,
        G=G,
        H=H,
        subsumptions=subsumptions,
    )
    # compute_role_chains now runs loop detection internally and raises error if loop found
    all_chains = extractor.compute_role_chains(
        max_length=max_length
    )
    paths_G = extractor.compute_paths(max_chain_length=max_length) if G is not None else []
    paths_H = extractor.aggregate_paths_with_H(paths_G) if H is not None and paths_G else []
    return {
        "all_chains": all_chains,
        "paths_G": paths_G,
        "paths_H": paths_H,
    }
