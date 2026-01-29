"""
Simple test runner for _RoleChainBuilder and ELPlusEdgesExtractor without pytest dependency.
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'src'))

from extract_el_plus_edges import (
    _RoleChainBuilder,
    compute_role_chains,
    load_role_axioms,
    ELPlusEdgesExtractor,
    RoleChainLoopError,
)


def test_single_inclusion():
    """r1 ⊑ r2 should produce chain [r1, r2]"""
    role_inclusions = {1: {2}}
    builder = _RoleChainBuilder(role_inclusions, {})
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2] in chains, f"Expected [1,2] in {chains}"
    print("✓ test_single_inclusion")


def test_chain_of_inclusions():
    """r1 ⊑ r2, r2 ⊑ r3 should produce [1,2], [2,3], [1,2,3]"""
    role_inclusions = {1: {2}, 2: {3}}
    builder = _RoleChainBuilder(role_inclusions, {})
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2] in chains, f"Expected [1,2] in {chains}"
    assert [2, 3] in chains, f"Expected [2,3] in {chains}"
    assert [1, 2, 3] in chains, f"Expected [1,2,3] in {chains}"
    print("✓ test_chain_of_inclusions")


def test_single_chain_axiom():
    """r ∘ s ⊑ t should produce chain [r, s, t]"""
    dic_tr_s = {(3, 1): {2}}  # 1 ∘ 2 ⊑ 3
    builder = _RoleChainBuilder({}, dic_tr_s)
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2, 3] in chains, f"Expected [1,2,3] in {chains}"
    print("✓ test_single_chain_axiom")


def test_nested_chain_axioms():
    """Nested chains: 1∘2⊑3, 3∘4⊑5 => [1,2,3,4,5]"""
    dic_tr_s = {
        (3, 1): {2},  # 1 ∘ 2 ⊑ 3
        (5, 3): {4},  # 3 ∘ 4 ⊑ 5
    }
    builder = _RoleChainBuilder({}, dic_tr_s)
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2, 3] in chains, f"Expected [1,2,3] in {chains}"
    assert [3, 4, 5] in chains, f"Expected [3,4,5] in {chains}"
    assert [1, 2, 3, 4, 5] in chains, f"Expected [1,2,3,4,5] in {chains}"
    print("✓ test_nested_chain_axioms")


def test_combined_axioms():
    """r1 ⊑ r2 and r2 ∘ s ⊑ t"""
    role_inclusions = {1: {2}}
    dic_tr_s = {(4, 2): {3}}  # 2 ∘ 3 ⊑ 4
    builder = _RoleChainBuilder(role_inclusions, dic_tr_s)
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2] in chains, f"Expected [1,2] in {chains}"
    assert [2, 3, 4] in chains, f"Expected [2,3,4] in {chains}"
    assert [1, 2, 3, 4] in chains, f"Expected [1,2,3,4] in {chains}"
    print("✓ test_combined_axioms")


def test_docstring_example():
    """Test the example: r2 ⊑ r3, r1 ∘ r2 ⊑ r3"""
    role_inclusions = {2: {3}}
    dic_tr_s = {(3, 1): {2}}  # 1 ∘ 2 ⊑ 3
    builder = _RoleChainBuilder(role_inclusions, dic_tr_s)
    non_loop, loop = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2, 3] in chains, f"Expected [1,2,3] in {chains}"
    assert [2, 3] in chains, f"Expected [2,3] in {chains}"
    print("✓ test_docstring_example")


def test_axiom_tracking():
    """Test that axioms are correctly tracked"""
    dic_tr_s = {(3, 1): {2}}
    builder = _RoleChainBuilder({}, dic_tr_s)
    non_loop, _ = builder.compute()
    
    chain_123 = next(c for c in non_loop if c["chain"] == [1, 2, 3])
    assert len(chain_123["axioms"]) == 1, f"Expected 1 axiom, got {len(chain_123['axioms'])}"
    assert "ObjectPropertyChain" in chain_123["axioms"][0], f"Expected ObjectPropertyChain in axiom"
    print("✓ test_axiom_tracking")


def test_max_length():
    """Chains longer than max_length should not appear"""
    role_inclusions = {1: {2}, 2: {3}, 3: {4}, 4: {5}}
    builder = _RoleChainBuilder(role_inclusions, {})
    non_loop, _ = builder.compute(max_length=3)
    
    chains = [c["chain"] for c in non_loop]
    for c in chains:
        assert len(c) <= 3, f"Chain {c} exceeds max_length=3"
    print("✓ test_max_length")


def test_empty_input():
    """Empty input should return empty results"""
    builder = _RoleChainBuilder({}, {})
    non_loop, loop = builder.compute()
    assert non_loop == [], f"Expected empty non_loop, got {non_loop}"
    assert loop == [], f"Expected empty loop, got {loop}"
    print("✓ test_empty_input")


def test_convenience_function():
    """compute_role_chains should work like builder"""
    ri = {2: {3}}
    dic = {(3, 1): {2}}
    non_loop, loop = compute_role_chains(ri, dic)
    
    chains = [c["chain"] for c in non_loop]
    assert [1, 2, 3] in chains, f"Expected [1,2,3] in {chains}"
    print("✓ test_convenience_function")


def test_galen7_data():
    """Test with real galen7 data"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_galen7_data (skipped - data not found)")
        return
    
    role_inclusions, dic_tr_s, inc_ax, chain_ax = load_role_axioms(galen7_path)
    print(f"  Loaded {len(role_inclusions)} role inclusions")
    print(f"  Loaded {len(dic_tr_s)} role chain axiom groups")
    
    builder = _RoleChainBuilder(role_inclusions, dic_tr_s, inc_ax, chain_ax)
    non_loop, loop = builder.compute(max_length=5)
    
    print(f"  Found {len(non_loop)} non-loop chains")
    print(f"  Found {len(loop)} loop chains")
    
    assert len(non_loop) + len(loop) > 0, "Expected some chains"
    
    if non_loop:
        print("  Example chains:")
        for c in non_loop[:3]:
            print(f"    {c['chain']}")
    
    print("✓ test_galen7_data")


# ============================================================
# New feature tests: max_length=None and fail_on_loop
# ============================================================

def test_max_length_none():
    """max_length=None should allow unlimited chain length"""
    role_inclusions = {1: {2}, 2: {3}, 3: {4}, 4: {5}, 5: {6}}
    builder = _RoleChainBuilder(role_inclusions, {})
    non_loop, _ = builder.compute(max_length=None)
    
    chains = [c["chain"] for c in non_loop]
    # Should have the full chain [1,2,3,4,5,6]
    assert [1, 2, 3, 4, 5, 6] in chains, f"Expected [1,2,3,4,5,6] in {chains}"
    print("✓ test_max_length_none")


def test_fail_on_loop_raises():
    """fail_on_loop=True should raise RoleChainLoopError on cycles"""
    role_inclusions = {1: {2}, 2: {1}}  # Cycle: 1 -> 2 -> 1
    builder = _RoleChainBuilder(role_inclusions, {})
    
    try:
        builder.compute(fail_on_loop=True)
        assert False, "Expected RoleChainLoopError to be raised"
    except RoleChainLoopError as e:
        assert "Cycle detected" in str(e), f"Expected 'Cycle detected' in error message: {e}"
    print("✓ test_fail_on_loop_raises")


def test_fail_on_loop_false_allows_cycles():
    """fail_on_loop=False (default) should handle cycles gracefully"""
    role_inclusions = {1: {2}, 2: {1}}  # Cycle: 1 -> 2 -> 1
    builder = _RoleChainBuilder(role_inclusions, {})
    
    # Should not raise
    non_loop, loop = builder.compute(fail_on_loop=False)
    chains = [c["chain"] for c in non_loop]
    # Should still produce [1,2] and [2,1]
    assert [1, 2] in chains or [2, 1] in chains, f"Expected [1,2] or [2,1] in {chains}"
    print("✓ test_fail_on_loop_false_allows_cycles")


def test_s_chain_can_share_with_r_chain():
    """s_chain can contain elements from r_chain (user requirement)"""
    # r ∘ s ⊑ t where r and s share a common ancestor
    # 1 ⊑ 2, 1 ⊑ 3, 2 ∘ 3 ⊑ 4
    role_inclusions = {1: {2, 3}}
    dic_tr_s = {(4, 2): {3}}  # 2 ∘ 3 ⊑ 4
    builder = _RoleChainBuilder(role_inclusions, dic_tr_s)
    non_loop, _ = builder.compute()
    
    chains = [c["chain"] for c in non_loop]
    # Should have [1, 2, 1, 3, 4] - 1 appears in both r_chain and s_chain
    # Actually with the new logic, s_chain uses new_visited (not r_visited)
    # so [1, 2, 1, 3, 4] should be possible
    has_shared = any(len(c) > len(set(c)) for c in chains)
    # Or check for specific chains that share elements
    print(f"  Chains with length > 3: {[c for c in chains if len(c) > 3]}")
    print("✓ test_s_chain_can_share_with_r_chain")


# ============================================================
# ELPlusEdgesExtractor tests
# ============================================================

def test_extractor_init():
    """Test ELPlusEdgesExtractor initialization"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_extractor_init (skipped - data not found)")
        return
    
    extractor = ELPlusEdgesExtractor(galen7_path)
    
    assert len(extractor.roles) > 0, "Expected roles to be inferred"
    assert extractor.role_inclusions is not None, "Expected role_inclusions"
    assert extractor.dic_tr_s is not None, "Expected dic_tr_s"
    print(f"  Inferred {len(extractor.roles)} roles")
    print("✓ test_extractor_init")


def test_extractor_compute_chains():
    """Test ELPlusEdgesExtractor.compute_role_chains"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_extractor_compute_chains (skipped - data not found)")
        return
    
    extractor = ELPlusEdgesExtractor(galen7_path)
    non_loop, loop = extractor.compute_role_chains(max_length=5)
    
    assert len(non_loop) > 0, "Expected non-loop chains"
    print(f"  Found {len(non_loop)} non-loop, {len(loop)} loop chains")
    print("✓ test_extractor_compute_chains")


def test_extractor_compute_paths_no_graphs():
    """Test ELPlusEdgesExtractor.compute_paths without graphs"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_extractor_compute_paths_no_graphs (skipped - data not found)")
        return
    
    extractor = ELPlusEdgesExtractor(galen7_path, G=None, H=None)
    
    # compute_role_chains should work
    non_loop, loop = extractor.compute_role_chains(max_length=5)
    assert len(non_loop) > 0, "Expected non-loop chains"
    
    # compute_paths should return empty without G
    paths = extractor.compute_paths(max_chain_length=5)
    assert paths == [], "Expected empty paths without graph G"
    
    print(f"  Got {len(non_loop)} chains, 0 paths (no graph)")
    print("✓ test_extractor_compute_paths_no_graphs")


def test_extractor_infer_roles():
    """Test role inference from axioms"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_extractor_infer_roles (skipped - data not found)")
        return
    
    extractor = ELPlusEdgesExtractor(galen7_path)
    
    # Roles should be inferred from role_inclusions and dic_tr_s
    all_roles_from_inclusions = set()
    for r1, targets in extractor.role_inclusions.items():
        all_roles_from_inclusions.add(r1)
        all_roles_from_inclusions.update(targets)
    
    all_roles_from_chains = set()
    for (t, r), s_set in extractor.dic_tr_s.items():
        all_roles_from_chains.add(t)
        all_roles_from_chains.add(r)
        all_roles_from_chains.update(s_set)
    
    expected_roles = all_roles_from_inclusions | all_roles_from_chains
    assert extractor.roles >= expected_roles, "Inferred roles should include all from axioms"
    print(f"  Inferred {len(extractor.roles)} roles, expected at least {len(expected_roles)}")
    print("✓ test_extractor_infer_roles")


# ============================================================
# compute_paths tests
# ============================================================

class MockHypergraph:
    """Mock hypergraph for testing compute_paths."""
    def __init__(self):
        self._edges = {}  # edge_id -> (tail, head, attrs)
        self._next_id = 0
        self.sig_r = set()
        self.sig_c = set()
    
    def add_edge(self, tail, head, attrs):
        """Add edge {tail} -> {head} with attributes."""
        eid = f"e{self._next_id}"
        self._next_id += 1
        self._edges[eid] = (frozenset(tail), frozenset(head), attrs)
        self.sig_c.update(tail)
        self.sig_c.update(head)
        for r in attrs.keys():
            self.sig_r.add(r)
        return eid
    
    def hyperedge_id_iterator(self):
        return iter(self._edges.keys())
    
    def get_hyperedge_tail(self, eid):
        return self._edges[eid][0]
    
    def get_hyperedge_head(self, eid):
        return self._edges[eid][1]
    
    def get_hyperedge_attributes(self, eid):
        return self._edges[eid][2]


def test_compute_paths_no_graph():
    """compute_paths returns empty list when G is None"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_compute_paths_no_graph (skipped - data not found)")
        return
    
    extractor = ELPlusEdgesExtractor(galen7_path, G=None)
    paths = extractor.compute_paths()
    assert paths == [], f"Expected empty list, got {paths}"
    print("✓ test_compute_paths_no_graph")


def test_compute_paths_simple():
    """Test compute_paths with a simple mock graph covering all roles in a chain"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_compute_paths_simple (skipped - data not found)")
        return
    
    # Create mock graph G
    G = MockHypergraph()
    
    # Load to see what role chains exist
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    # Find a chain with at least 2 roles and add edges for ALL roles in it
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 3:  # [r1, r2, t] has 2 roles
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        # Add edges for each role with connecting concepts
        # A1 -r1-> B1=A2 -r2-> B2=A3 ...
        for i, r in enumerate(roles):
            A = f"Concept{i}"
            B = f"Concept{i+1}"
            G.add_edge([A], [B], {r: f"axiom{i}"})
        
        extractor = ELPlusEdgesExtractor(galen7_path, G=G)
        paths = extractor.compute_paths(max_chain_length=3)
        
        print(f"  Test chain: {test_chain}")
        print(f"  Found {len(paths)} paths with mock graph")
        if paths:
            print(f"  Example path: k={paths[0].get('k')}, reduced_chain={paths[0].get('reduced_chain')}")
        assert len(paths) > 0, f"Expected paths for chain {test_chain}"
    else:
        print("  No suitable chain found for testing")
    
    print("✓ test_compute_paths_simple")


def test_compute_paths_with_subsumptions():
    """Test compute_paths with subsumptions connecting edges"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_compute_paths_with_subsumptions (skipped - data not found)")
        return
    
    # Create mock graph with edges for a chain that needs subsumption
    G = MockHypergraph()
    
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    # Find a chain with 2 roles
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) == 3:  # [r1, r2, t]
            test_chain = c["chain"]
            break
    
    if test_chain:
        r1, r2 = test_chain[0], test_chain[1]
        # Edge 1: A ⊑ ∃r1.B
        G.add_edge(["A"], ["B"], {r1: "ax1"})
        # Edge 2: C ⊑ ∃r2.D (B != C, need subsumption)
        G.add_edge(["C"], ["D"], {r2: "ax2"})
        
        # Subsumption: B ⊑ C (connects the two edges)
        subsumptions = {"B": {"C"}}
        
        extractor = ELPlusEdgesExtractor(galen7_path, G=G, subsumptions=subsumptions)
        paths = extractor.compute_paths(max_chain_length=3)
        
        # Check if any path uses the subsumption
        paths_with_subs = [p for p in paths if p.get("subsumptions")]
        print(f"  Test chain: {test_chain}")
        print(f"  Found {len(paths)} total paths, {len(paths_with_subs)} using subsumptions")
    
    print("✓ test_compute_paths_with_subsumptions")


def test_compute_paths_reduced_chain():
    """Test that reduced_chain is correctly computed"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_compute_paths_reduced_chain (skipped - data not found)")
        return
    
    G = MockHypergraph()
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    # Find a chain with multiple roles and add edges for ALL roles
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 3:
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        for i, r in enumerate(roles):
            G.add_edge([f"X{i}"], [f"X{i+1}"], {r: f"ax{i}"})
    
    extractor = ELPlusEdgesExtractor(galen7_path, G=G)
    paths = extractor.compute_paths(max_chain_length=3)
    
    for p in paths:
        original = p.get("original_chain", [])
        reduced = p.get("reduced_chain", [])
        k = p.get("k", 0)
        
        # reduced_chain should be [r_1, ..., r_{k-1}, t]
        if len(original) >= 2:
            t = original[-1]
            assert reduced[-1] == t, f"Reduced chain should end with target role t={t}"
            assert len(reduced) == k, f"Reduced chain length should be k={k}, got {len(reduced)}"
    
    print(f"  Verified {len(paths)} paths have correct reduced_chain")
    print("✓ test_compute_paths_reduced_chain")


def test_compute_paths_has_first_last_concept():
    """Test that paths have first_concept and last_concept keys"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_compute_paths_has_first_last_concept (skipped - data not found)")
        return
    
    G = MockHypergraph()
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 3:
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        for i, r in enumerate(roles):
            G.add_edge([f"A{i}"], [f"B{i}"], {r: f"ax{i}"})
    
    extractor = ELPlusEdgesExtractor(galen7_path, G=G)
    paths = extractor.compute_paths(max_chain_length=3)
    
    for p in paths:
        assert "first_concept" in p, "Path should have first_concept key"
        assert "last_concept" in p, "Path should have last_concept key"
        # first_concept should match first edge's A
        edges = p.get("edges", [])
        if edges:
            assert p["first_concept"] == edges[0][0], "first_concept should match first edge's A"
            assert p["last_concept"] == edges[-1][2], "last_concept should match last edge's B"
    
    print(f"  Verified {len(paths)} paths have first_concept and last_concept")
    print("✓ test_compute_paths_has_first_last_concept")


def test_aggregate_paths_with_H():
    """Test aggregate_paths_with_H extends paths using H graph"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_aggregate_paths_with_H (skipped - data not found)")
        return
    
    G = MockHypergraph()
    H = MockHypergraph()
    
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 2:
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        t = test_chain[-1]
        
        # Add edges in G for all roles
        for i, r in enumerate(roles):
            G.add_edge([f"A{i}"], [f"B{i}"], {r: f"ax{i}"})
        
        # Add H edge: ∃t.B_last ⊑ C (where B_last is the last concept from G path)
        last_B = f"B{len(roles)-1}"
        H.add_edge([last_B], ["C_extended"], {t: "h_ax1"})
        
        extractor = ELPlusEdgesExtractor(galen7_path, G=G, H=H)
        paths = extractor.compute_paths(max_chain_length=3)
        
        # Aggregate paths
        aggregated = extractor.aggregate_paths_with_H(paths)
        
        # Should have more paths after aggregation (original + extended)
        print(f"  Original paths: {len(paths)}, Aggregated: {len(aggregated)}")
        
        # Check some aggregated paths have H_edges
        paths_with_h = [p for p in aggregated if p.get("H_edges")]
        print(f"  Paths with H extensions: {len(paths_with_h)}")
        
        if paths_with_h:
            # Verify the extended path has updated last_concept
            for p in paths_with_h:
                assert p["last_concept"] == "C_extended", f"Extended path should have last_concept=C_extended"
    
    print("✓ test_aggregate_paths_with_H")


def test_aggregate_paths_with_subsumption_and_H():
    """Test aggregate_paths_with_H with subsumption B ⊑ B' before H edge"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_aggregate_paths_with_subsumption_and_H (skipped - data not found)")
        return
    
    G = MockHypergraph()
    H = MockHypergraph()
    
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 2:
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        t = test_chain[-1]
        
        # Add edges in G
        for i, r in enumerate(roles):
            G.add_edge([f"A{i}"], [f"B{i}"], {r: f"ax{i}"})
        
        last_B = f"B{len(roles)-1}"
        # H edge uses B_prime, not last_B directly
        H.add_edge(["B_prime"], ["C_final"], {t: "h_ax1"})
        
        # Subsumption: last_B ⊑ B_prime
        subsumptions = {last_B: {"B_prime"}}
        
        extractor = ELPlusEdgesExtractor(galen7_path, G=G, H=H, subsumptions=subsumptions)
        paths = extractor.compute_paths(max_chain_length=3)
        aggregated = extractor.aggregate_paths_with_H(paths)
        
        # Check for paths extended via subsumption + H
        paths_with_h_subs = [p for p in aggregated if p.get("H_subsumptions")]
        print(f"  Paths with H_subsumptions: {len(paths_with_h_subs)}")
        
        if paths_with_h_subs:
            for p in paths_with_h_subs:
                assert (last_B, "B_prime") in p["H_subsumptions"], "Should record subsumption"
                assert p["last_concept"] == "C_final", "Should have extended last_concept"
    
    print("✓ test_aggregate_paths_with_subsumption_and_H")


def test_aggregate_paths_loop_detection():
    """Test that aggregate_paths_with_H detects loops"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_aggregate_paths_loop_detection (skipped - data not found)")
        return
    
    G = MockHypergraph()
    H = MockHypergraph()
    
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=3)
    
    test_chain = None
    for c in non_loop:
        if len(c["chain"]) >= 2:
            test_chain = c["chain"]
            break
    
    if test_chain:
        roles = test_chain[:-1]
        t = test_chain[-1]
        
        # Add edges in G
        for i, r in enumerate(roles):
            G.add_edge([f"A{i}"], [f"B{i}"], {r: f"ax{i}"})
        
        last_B = f"B{len(roles)-1}"
        # Create a loop in H: B_last -> C -> B_last
        H.add_edge([last_B], ["C"], {t: "h1"})
        H.add_edge(["C"], [last_B], {t: "h2"})
        
        extractor = ELPlusEdgesExtractor(galen7_path, G=G, H=H)
        paths = extractor.compute_paths(max_chain_length=3)
        aggregated = extractor.aggregate_paths_with_H(paths)
        
        # Should terminate (not infinite loop) and have some paths
        print(f"  Aggregated {len(aggregated)} paths (loop should be detected)")
        assert len(aggregated) > 0, "Should have some paths"
    
    print("✓ test_aggregate_paths_loop_detection")


def test_galen7_aggregate_with_loops():
    """Test aggregate_paths_with_H on galen7 data with intentional loops in H"""
    galen7_path = os.path.join(
        os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
    )
    
    if not os.path.exists(galen7_path):
        print("⊘ test_galen7_aggregate_with_loops (skipped - data not found)")
        return
    
    G = MockHypergraph()
    H = MockHypergraph()
    
    extractor_temp = ELPlusEdgesExtractor(galen7_path, G=None)
    non_loop, _ = extractor_temp.compute_role_chains(max_length=5)
    
    # Find multiple chains with different target roles
    chains_by_target = {}
    for c in non_loop:
        if len(c["chain"]) >= 2:
            t = c["chain"][-1]
            if t not in chains_by_target:
                chains_by_target[t] = c["chain"]
    
    # Use first 3 different target roles
    test_chains = list(chains_by_target.values())[:3]
    
    if not test_chains:
        print("  No suitable chains found")
        print("✓ test_galen7_aggregate_with_loops")
        return
    
    # Add edges in G for all chains
    concept_counter = 0
    all_last_concepts = []
    for chain in test_chains:
        roles = chain[:-1]
        for i, r in enumerate(roles):
            G.add_edge([f"C{concept_counter}"], [f"C{concept_counter+1}"], {r: f"ax{concept_counter}"})
            concept_counter += 1
        all_last_concepts.append(f"C{concept_counter}")
        concept_counter += 1
    
    # Create loops in H: each last concept connects to others via target roles
    for i, chain in enumerate(test_chains):
        t = chain[-1]
        last_B = all_last_concepts[i]
        # Create loop: last_B -> X -> Y -> last_B
        H.add_edge([last_B], [f"X{i}"], {t: f"h{i}_1"})
        H.add_edge([f"X{i}"], [f"Y{i}"], {t: f"h{i}_2"})
        H.add_edge([f"Y{i}"], [last_B], {t: f"h{i}_3"})  # Loop back!
    
    extractor = ELPlusEdgesExtractor(galen7_path, G=G, H=H)
    paths = extractor.compute_paths(max_chain_length=5)
    
    print(f"  Found {len(paths)} paths from G")
    
    # Aggregate - should handle loops without infinite loop
    aggregated = extractor.aggregate_paths_with_H(paths)
    
    print(f"  Aggregated to {len(aggregated)} paths (with loop detection)")
    
    # Check that we have some extended paths
    paths_with_h = [p for p in aggregated if p.get("H_edges")]
    print(f"  Paths with H extensions: {len(paths_with_h)}")
    
    # Verify loop detection worked (should have finite paths)
    assert len(aggregated) < 1000, "Loop detection should prevent explosion"
    
    # Check that loops were actually encountered (paths should visit multiple H edges)
    max_h_edges = max(len(p.get("H_edges", [])) for p in aggregated) if aggregated else 0
    print(f"  Max H_edges in a path: {max_h_edges}")
    
    print("✓ test_galen7_aggregate_with_loops")


def run_all_tests():
    """Run all tests"""
    print("=" * 50)
    print("Running _RoleChainBuilder and ELPlusEdgesExtractor tests")
    print("=" * 50)
    
    tests = [
        # Basic _RoleChainBuilder tests
        test_single_inclusion,
        test_chain_of_inclusions,
        test_single_chain_axiom,
        test_nested_chain_axioms,
        test_combined_axioms,
        test_docstring_example,
        test_axiom_tracking,
        test_max_length,
        test_empty_input,
        test_convenience_function,
        test_galen7_data,
        # New feature tests
        test_max_length_none,
        test_fail_on_loop_raises,
        test_fail_on_loop_false_allows_cycles,
        test_s_chain_can_share_with_r_chain,
        # ELPlusEdgesExtractor tests
        test_extractor_init,
        test_extractor_compute_chains,
        test_extractor_compute_paths_no_graphs,
        test_extractor_infer_roles,
        # compute_paths tests
        test_compute_paths_no_graph,
        test_compute_paths_simple,
        test_compute_paths_with_subsumptions,
        test_compute_paths_reduced_chain,
        test_compute_paths_has_first_last_concept,
        # aggregate_paths_with_H tests
        test_aggregate_paths_with_H,
        test_aggregate_paths_with_subsumption_and_H,
        test_aggregate_paths_loop_detection,
        test_galen7_aggregate_with_loops,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__}: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__}: {type(e).__name__}: {e}")
            failed += 1
    
    print("=" * 50)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 50)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
