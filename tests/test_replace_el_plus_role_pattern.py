"""
Unit tests for replace_el_plus_role_pattern function.

Tests cover:
1. Case 1: (some <-r1-r2...-rn+t> C1) -> (some <t> C1) with placeholder
2. Case 2: (some <-r1-r2...-rn> C1) -> nested some expressions
3. Case 3: (some <+t> C1) -> (some <t> C1)
4. Case 4: Regular expressions (no change)
5. Recursive processing with (and ...) conjunctions
6. Mode constraints (Case 1 only first, Case 2 excludes Case 3, etc.)
7. Edge cases
"""

import sys
import os
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from ForMod import replace_el_plus_role_pattern


class TestCase1_ChainWithTarget:
    """Test Case 1: (some <-r1-r2...-rn+t> C1) patterns"""
    
    def test_single_chain_role_with_target(self):
        """(some <-r1+t> <A>) -> (some <t> <A>), placeholder: (some <r1> X)"""
        expr = "(some <-r1+t> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> <A>)"
        assert placeholder == "(some <r1> X)"
    
    def test_two_chain_roles_with_target(self):
        """(some <-r1-r2+t> <A>) -> (some <t> <A>), placeholder: (some <r1> (some <r2> X))"""
        expr = "(some <-r1-r2+t> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> <A>)"
        assert placeholder == "(some <r1> (some <r2> X))"
    
    def test_three_chain_roles_with_target(self):
        """(some <-r1-r2-r3+t> <A>) -> nested placeholder"""
        expr = "(some <-r1-r2-r3+t> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> <A>)"
        assert placeholder == "(some <r1> (some <r2> (some <r3> X)))"
    
    def test_case1_with_nested_some_inner(self):
        """Case 1 with nested (some ...) as inner concept"""
        expr = "(some <-r1+t> (some <s> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> (some <s> <B>))"
        assert placeholder == "(some <r1> X)"
    
    def test_case1_with_case3_nested(self):
        """Case 1 followed by Case 3 in inner concept"""
        expr = "(some <-r1+t> (some <+s> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        # Inner (some <+s> <B>) should become (some <s> <B>)
        assert result == "(some <t> (some <s> <B>))"
        assert placeholder == "(some <r1> X)"


class TestCase2_ChainWithoutTarget:
    """Test Case 2: (some <-r1-r2...-rn> C1) patterns"""
    
    def test_single_chain_role(self):
        """(some <-r1> <A>) -> (some <r1> <A>)"""
        expr = "(some <-r1> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> <A>)"
        assert placeholder == ""
    
    def test_two_chain_roles(self):
        """(some <-r1-r2> <A>) -> (some <r1> (some <r2> <A>))"""
        expr = "(some <-r1-r2> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> (some <r2> <A>))"
        assert placeholder == ""
    
    def test_three_chain_roles(self):
        """(some <-r1-r2-r3> <A>) -> nested some expressions"""
        expr = "(some <-r1-r2-r3> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> (some <r2> (some <r3> <A>)))"
        assert placeholder == ""
    
    def test_case2_with_nested_case2(self):
        """Case 2 with nested Case 2"""
        expr = "(some <-r1-r2> (some <-s1-s2> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        # Inner should become (some <s1> (some <s2> <A>))
        # Outer wraps that
        expected = "(some <r1> (some <r2> (some <s1> (some <s2> <A>))))"
        assert result == expected
        assert placeholder == ""
    
    def test_case2_with_regular_nested(self):
        """Case 2 with regular (some <role> ...) nested"""
        expr = "(some <-r1-r2> (some <s> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(some <r1> (some <r2> (some <s> <A>)))"
        assert result == expected
        assert placeholder == ""


class TestCase3_PlusOnly:
    """Test Case 3: (some <+t> C1) patterns"""
    
    def test_simple_plus_role(self):
        """(some <+t> <A>) -> (some <t> <A>)"""
        expr = "(some <+t> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> <A>)"
        assert placeholder == ""
    
    def test_plus_role_with_nested_some(self):
        """(some <+t> (some <s> <A>)) -> (some <t> (some <s> <A>))"""
        expr = "(some <+t> (some <s> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> (some <s> <A>))"
        assert placeholder == ""
    
    def test_nested_plus_roles(self):
        """Nested Case 3 patterns"""
        expr = "(some <+t1> (some <+t2> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t1> (some <t2> <A>))"
        assert placeholder == ""


class TestCase4_Regular:
    """Test Case 4: Regular expressions (no special pattern)"""
    
    def test_atomic_concept(self):
        """<A> -> <A> (no change)"""
        expr = "<A>"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "<A>"
        assert placeholder == ""
    
    def test_regular_some(self):
        """(some <r> <A>) -> (some <r> <A>) (no change)"""
        expr = "(some <r> <A>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r> <A>)"
        assert placeholder == ""
    
    def test_nested_regular_some(self):
        """Nested regular some expressions"""
        expr = "(some <r1> (some <r2> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> (some <r2> <A>))"
        assert placeholder == ""


class TestAndConjunctions:
    """Test (and ...) conjunction handling"""
    
    def test_simple_and(self):
        """(and <A> <B>) -> (and <A> <B>)"""
        expr = "(and <A> <B>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(and <A> <B>)"
        assert placeholder == ""
    
    def test_and_with_some(self):
        """(and <A> (some <r> <B>)) -> unchanged"""
        expr = "(and <A> (some <r> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(and <A> (some <r> <B>))"
        assert placeholder == ""
    
    def test_and_with_case2(self):
        """(and <A> (some <-r1-r2> <B>)) -> expanded"""
        expr = "(and <A> (some <-r1-r2> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(and <A> (some <r1> (some <r2> <B>)))"
        assert result == expected
        assert placeholder == ""
    
    def test_and_with_case3(self):
        """(and <A> (some <+t> <B>)) -> plus removed"""
        expr = "(and <A> (some <+t> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(and <A> (some <t> <B>))"
        assert result == expected
        assert placeholder == ""
    
    def test_and_with_multiple_special_patterns(self):
        """(and (some <-r1> <A>) (some <+t> <B>)) -> both processed"""
        expr = "(and (some <-r1> <A>) (some <+t> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(and (some <r1> <A>) (some <t> <B>))"
        assert result == expected
        assert placeholder == ""
    
    def test_three_conjuncts(self):
        """(and <A> <B> <C>) -> unchanged"""
        expr = "(and <A> <B> <C>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(and <A> <B> <C>)"
        assert placeholder == ""


class TestModeConstraints:
    """Test mode constraints from docstring"""
    
    def test_case2_after_case1_raises_error(self):
        """Case 2 should not appear after Case 1"""
        # This would be: (some <-r+t> (some <-s1-s2> <A>))
        # After Case 1 processes outer, inner should only be Case 3 or 4
        expr = "(some <-r+t> (some <-s1-s2> <A>))"
        
        with pytest.raises(ValueError, match="Case 2 pattern found after Case 1"):
            replace_el_plus_role_pattern(expr)
    
    def test_case3_after_case2_raises_error(self):
        """Case 3 should not appear after Case 2"""
        # This would be: (some <-r1-r2> (some <+t> <A>))
        # After Case 2 processes outer, inner should only be Case 2 or 4
        expr = "(some <-r1-r2> (some <+t> <A>))"
        
        with pytest.raises(ValueError, match="Case 3 pattern found after Case 2"):
            replace_el_plus_role_pattern(expr)
    
    def test_case1_nested_raises_error(self):
        """Case 1 should only happen at top level"""
        # Nested Case 1 should raise error
        expr = "(some <-r+t> (some <-s+u> <A>))"
        
        with pytest.raises(ValueError, match="Case 1 pattern found in non-initial mode"):
            replace_el_plus_role_pattern(expr)
    
    def test_case3_after_case1_is_valid(self):
        """Case 3 after Case 1 is valid"""
        expr = "(some <-r+t> (some <+s> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> (some <s> <A>))"
        assert placeholder == "(some <r> X)"
    
    def test_case4_after_case1_is_valid(self):
        """Case 4 after Case 1 is valid"""
        expr = "(some <-r+t> (some <s> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> (some <s> <A>))"
        assert placeholder == "(some <r> X)"
    
    def test_case2_after_case2_is_valid(self):
        """Case 2 after Case 2 is valid"""
        expr = "(some <-r1> (some <-s1-s2> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(some <r1> (some <s1> (some <s2> <A>)))"
        assert result == expected
        assert placeholder == ""
    
    def test_case4_after_case2_is_valid(self):
        """Case 4 after Case 2 is valid"""
        expr = "(some <-r1-r2> (some <s> <A>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(some <r1> (some <r2> (some <s> <A>)))"
        assert result == expected
        assert placeholder == ""


class TestComplexExpressions:
    """Test complex nested expressions"""
    
    def test_deeply_nested_case2(self):
        """Deeply nested Case 2 patterns"""
        expr = "(some <-r1> (some <-r2> (some <-r3> <A>)))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(some <r1> (some <r2> (some <r3> <A>)))"
        assert result == expected
        assert placeholder == ""
    
    def test_and_inside_some(self):
        """(some <r> (and <A> <B>)) -> unchanged"""
        expr = "(some <r> (and <A> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r> (and <A> <B>))"
        assert placeholder == ""
    
    def test_case2_with_and_inner(self):
        """(some <-r1-r2> (and <A> <B>)) -> expanded"""
        expr = "(some <-r1-r2> (and <A> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(some <r1> (some <r2> (and <A> <B>)))"
        assert result == expected
        assert placeholder == ""
    
    def test_case1_with_and_inner(self):
        """(some <-r+t> (and <A> <B>)) -> processed"""
        expr = "(some <-r+t> (and <A> <B>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <t> (and <A> <B>))"
        assert placeholder == "(some <r> X)"
    
    def test_and_with_nested_and(self):
        """(and <A> (and <B> <C>)) -> unchanged"""
        expr = "(and <A> (and <B> <C>))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(and <A> (and <B> <C>))"
        assert placeholder == ""


class TestRealWorldPatterns:
    """Test patterns that might appear in real ontologies"""
    
    def test_role_chain_pattern_from_g(self):
        """Pattern from G paths: -r1-r2+t format"""
        expr = "(some <-hasParent-hasSibling+hasUncle> <Person>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <hasUncle> <Person>)"
        assert placeholder == "(some <hasParent> (some <hasSibling> X))"
    
    def test_role_chain_pattern_from_h(self):
        """Pattern from H paths: -r1-r2 format"""
        expr = "(some <-hasParent-hasSibling> <Person>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <hasParent> (some <hasSibling> <Person>))"
        assert placeholder == ""
    
    def test_simple_target_role(self):
        """Pattern: +t format (simple target role)"""
        expr = "(some <+hasUncle> <Person>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <hasUncle> <Person>)"
        assert placeholder == ""
    
    def test_complex_ontology_pattern(self):
        """Complex pattern with multiple levels"""
        expr = "(and <Animal> (some <-r1-r2> (and <Mammal> (some <-s1> <Vertebrate>))))"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        expected = "(and <Animal> (some <r1> (some <r2> (and <Mammal> (some <s1> <Vertebrate>)))))"
        assert result == expected
        assert placeholder == ""


class TestEdgeCases:
    """Test edge cases"""
    
    def test_empty_string(self):
        """Empty string input"""
        expr = ""
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == ""
        assert placeholder == ""
    
    def test_whitespace_handling(self):
        """Whitespace in expression"""
        expr = "  (some <-r1-r2> <A>)  "
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> (some <r2> <A>))"
        assert placeholder == ""
    
    def test_role_name_with_numbers(self):
        """Role names containing numbers"""
        expr = "(some <-role1-role2+target3> <Concept4>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <target3> <Concept4>)"
        assert placeholder == "(some <role1> (some <role2> X))"
    
    def test_role_name_with_underscores(self):
        """Role names with underscores"""
        expr = "(some <-has_parent-has_sibling> <Person>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <has_parent> (some <has_sibling> <Person>))"
        assert placeholder == ""
    
    def test_concept_name_with_special_chars(self):
        """Concept names with special characters"""
        expr = "(some <-r1> <http://example.org/Concept>)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> <http://example.org/Concept>)"
        assert placeholder == ""
    
    def test_owl_thing(self):
        """owl:Thing as concept"""
        expr = "(some <-r1-r2> owl:Thing)"
        result, placeholder = replace_el_plus_role_pattern(expr)
        
        assert result == "(some <r1> (some <r2> owl:Thing))"
        assert placeholder == ""


class TestReturnValues:
    """Test return value structure"""
    
    def test_returns_tuple(self):
        """Function should return a tuple of two strings"""
        result = replace_el_plus_role_pattern("<A>")
        
        assert isinstance(result, tuple)
        assert len(result) == 2
        assert isinstance(result[0], str)
        assert isinstance(result[1], str)
    
    def test_placeholder_only_for_case1(self):
        """Placeholder should only be non-empty for Case 1"""
        # Case 1
        _, ph1 = replace_el_plus_role_pattern("(some <-r+t> <A>)")
        assert ph1 != ""
        
        # Case 2
        _, ph2 = replace_el_plus_role_pattern("(some <-r1-r2> <A>)")
        assert ph2 == ""
        
        # Case 3
        _, ph3 = replace_el_plus_role_pattern("(some <+t> <A>)")
        assert ph3 == ""
        
        # Case 4
        _, ph4 = replace_el_plus_role_pattern("(some <r> <A>)")
        assert ph4 == ""


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
