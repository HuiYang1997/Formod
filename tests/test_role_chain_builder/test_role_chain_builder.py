"""
Unit tests for _RoleChainBuilder class.

Tests cover:
1. Simple role inclusions (r1 ⊑ r2)
2. Role chain axioms (r ∘ s ⊑ t)
3. Combined axioms
4. Loop detection
5. Real data from galen7
"""

import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'src'))

from extract_el_plus_edges import (
    _RoleChainBuilder,
    compute_role_chains,
    load_role_axioms,
    ELPlusEdgesExtractor,
)


class TestBasicRoleInclusions:
    """Test simple role inclusion axioms: r1 ⊑ r2"""
    
    def test_single_inclusion(self):
        """r1 ⊑ r2 should produce chain [r1, r2]"""
        role_inclusions = {1: {2}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2] in chains
    
    def test_chain_of_inclusions(self):
        """r1 ⊑ r2, r2 ⊑ r3 should produce [1,2], [2,3], [1,2,3]"""
        role_inclusions = {1: {2}, 2: {3}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2] in chains
        assert [2, 3] in chains
        assert [1, 2, 3] in chains
    
    def test_branching_inclusions(self):
        """r1 ⊑ r3, r2 ⊑ r3 should produce separate chains"""
        role_inclusions = {1: {3}, 2: {3}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 3] in chains
        assert [2, 3] in chains
    
    def test_self_inclusion_ignored(self):
        """r ⊑ r should be ignored"""
        role_inclusions = {1: {1, 2}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2] in chains
        # [1, 1] should not exist
        assert [1, 1] not in chains


class TestRoleChainAxioms:
    """Test role chain axioms: r ∘ s ⊑ t"""
    
    def test_single_chain_axiom(self):
        """r ∘ s ⊑ t should produce chain [r, s, t]"""
        dic_tr_s = {(3, 1): {2}}  # 1 ∘ 2 ⊑ 3
        builder = _RoleChainBuilder({}, dic_tr_s)
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2, 3] in chains
    
    def test_multiple_chain_axioms_same_target(self):
        """Multiple chain axioms to same target"""
        dic_tr_s = {
            (5, 1): {2},  # 1 ∘ 2 ⊑ 5
            (5, 3): {4},  # 3 ∘ 4 ⊑ 5
        }
        builder = _RoleChainBuilder({}, dic_tr_s)
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2, 5] in chains
        assert [3, 4, 5] in chains
    
    def test_nested_chain_axioms(self):
        """Nested chains: 1∘2⊑3, 3∘4⊑5 => [1,2,3,4,5]"""
        dic_tr_s = {
            (3, 1): {2},  # 1 ∘ 2 ⊑ 3
            (5, 3): {4},  # 3 ∘ 4 ⊑ 5
        }
        builder = _RoleChainBuilder({}, dic_tr_s)
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2, 3] in chains
        assert [3, 4, 5] in chains
        assert [1, 2, 3, 4, 5] in chains


class TestCombinedAxioms:
    """Test combination of role inclusions and chain axioms"""
    
    def test_inclusion_and_chain(self):
        """r1 ⊑ r2 and r2 ∘ s ⊑ t"""
        role_inclusions = {1: {2}}
        dic_tr_s = {(4, 2): {3}}  # 2 ∘ 3 ⊑ 4
        builder = _RoleChainBuilder(role_inclusions, dic_tr_s)
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2] in chains
        assert [2, 3, 4] in chains
        # Should derive [1, 2, 3, 4] via 1⊑2 then 2∘3⊑4
        assert [1, 2, 3, 4] in chains
    
    def test_docstring_example(self):
        """Test the example: r2 ⊑ r3, r1 ∘ r2 ⊑ r3"""
        role_inclusions = {2: {3}}
        dic_tr_s = {(3, 1): {2}}  # 1 ∘ 2 ⊑ 3
        builder = _RoleChainBuilder(role_inclusions, dic_tr_s)
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2, 3] in chains
        assert [2, 3] in chains


class TestLoopDetection:
    """Test loop detection"""
    
    def test_simple_loop(self):
        """r1 ⊑ r2, r2 ⊑ r1 forms a loop"""
        role_inclusions = {1: {2}, 2: {1}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        # Should still produce [1,2] and [2,1] but they're non-looped individually
        chains = [c["chain"] for c in non_loop]
        assert [1, 2] in chains or [2, 1] in chains
    
    def test_duplicate_in_chain_is_loop(self):
        """Chain with duplicate role is marked as loop"""
        # This would require a specific axiom structure
        # For now, test that chains with duplicates go to loop list
        pass
    
    def test_acyclic_graph(self):
        """Acyclic graph produces no loop chains"""
        role_inclusions = {1: {2}, 2: {3}, 3: {4}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, loop = builder.compute()
        
        # All chains should be non-loop
        assert len(loop) == 0
        assert len(non_loop) > 0


class TestAxiomTracking:
    """Test that axioms are correctly tracked"""
    
    def test_inclusion_axiom_tracked(self):
        """Role inclusion axiom should be in result"""
        role_inclusions = {1: {2}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, _ = builder.compute()
        
        chain_12 = next(c for c in non_loop if c["chain"] == [1, 2])
        assert len(chain_12["axioms"]) == 1
        assert "SubObjectPropertyOf" in chain_12["axioms"][0]
    
    def test_chain_axiom_tracked(self):
        """Role chain axiom should be in result"""
        dic_tr_s = {(3, 1): {2}}
        builder = _RoleChainBuilder({}, dic_tr_s)
        non_loop, _ = builder.compute()
        
        chain_123 = next(c for c in non_loop if c["chain"] == [1, 2, 3])
        assert len(chain_123["axioms"]) == 1
        assert "ObjectPropertyChain" in chain_123["axioms"][0]


class TestConvenienceFunction:
    """Test compute_role_chains wrapper"""
    
    def test_basic_usage(self):
        """compute_role_chains should work like builder"""
        ri = {2: {3}}
        dic = {(3, 1): {2}}
        non_loop, loop = compute_role_chains(ri, dic)
        
        chains = [c["chain"] for c in non_loop]
        assert [1, 2, 3] in chains


class TestMaxLength:
    """Test max_length parameter"""
    
    def test_max_length_limits_chains(self):
        """Chains longer than max_length should not appear"""
        role_inclusions = {1: {2}, 2: {3}, 3: {4}, 4: {5}}
        builder = _RoleChainBuilder(role_inclusions, {})
        non_loop, _ = builder.compute(max_length=3)
        
        chains = [c["chain"] for c in non_loop]
        # Should have [1,2], [2,3], [3,4], [4,5], [1,2,3], [2,3,4], [3,4,5]
        # But NOT [1,2,3,4] or longer
        for c in chains:
            assert len(c) <= 3


class TestGalen7Data:
    """Test with real galen7 data"""
    
    @pytest.fixture
    def galen7_path(self):
        return os.path.join(
            os.path.dirname(__file__), '..', '..', 'workspace', 'galen7', 'data'
        )
    
    def test_load_role_axioms(self, galen7_path):
        """Test loading axioms from galen7"""
        if not os.path.exists(galen7_path):
            pytest.skip("galen7 data not found")
        
        role_inclusions, dic_tr_s, inc_ax, chain_ax = load_role_axioms(galen7_path)
        
        # Should have loaded some data
        assert len(role_inclusions) > 0 or len(dic_tr_s) > 0
        print(f"Loaded {len(role_inclusions)} role inclusions")
        print(f"Loaded {len(dic_tr_s)} role chain axiom groups")
    
    def test_compute_chains_from_galen7(self, galen7_path):
        """Test computing chains from galen7 data"""
        if not os.path.exists(galen7_path):
            pytest.skip("galen7 data not found")
        
        role_inclusions, dic_tr_s, inc_ax, chain_ax = load_role_axioms(galen7_path)
        builder = _RoleChainBuilder(role_inclusions, dic_tr_s, inc_ax, chain_ax)
        non_loop, loop = builder.compute(max_length=5)
        
        print(f"Found {len(non_loop)} non-loop chains")
        print(f"Found {len(loop)} loop chains")
        
        # Should produce some chains
        assert len(non_loop) + len(loop) > 0
        
        # Print some example chains
        if non_loop:
            print("Example non-loop chains:")
            for c in non_loop[:5]:
                print(f"  {c['chain']}")
    
    def test_extractor_with_galen7(self, galen7_path):
        """Test ELPlusEdgesExtractor with galen7"""
        if not os.path.exists(galen7_path):
            pytest.skip("galen7 data not found")
        
        extractor = ELPlusEdgesExtractor(galen7_path)
        non_loop, loop = extractor.compute_role_chains(max_length=5)
        
        print(f"Extractor found {len(non_loop)} non-loop, {len(loop)} loop chains")
        assert len(non_loop) + len(loop) > 0


class TestEdgeCases:
    """Test edge cases"""
    
    def test_empty_input(self):
        """Empty input should return empty results"""
        builder = _RoleChainBuilder({}, {})
        non_loop, loop = builder.compute()
        assert non_loop == []
        assert loop == []
    
    def test_single_role_no_axioms(self):
        """Single role with no axioms"""
        builder = _RoleChainBuilder({}, {}, roles={1})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1] in chains
    
    def test_disconnected_roles(self):
        """Disconnected roles should each form single-element chains"""
        builder = _RoleChainBuilder({}, {}, roles={1, 2, 3})
        non_loop, loop = builder.compute()
        
        chains = [c["chain"] for c in non_loop]
        assert [1] in chains
        assert [2] in chains
        assert [3] in chains


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
