"""
Standalone test runner for replace_el_plus_role_pattern function.
Does not require pytest.
"""

import sys
import os
import traceback

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from ForMod import replace_el_plus_role_pattern


def test(name, condition, msg=""):
    """Simple test assertion."""
    if condition:
        print(f"  ✓ {name}")
        return True
    else:
        print(f"  ✗ {name}: {msg}")
        return False


def test_eq(name, actual, expected):
    """Test equality."""
    if actual == expected:
        print(f"  ✓ {name}")
        return True
    else:
        print(f"  ✗ {name}")
        print(f"      Expected: {expected}")
        print(f"      Actual:   {actual}")
        return False


def test_raises(name, func, expected_error_substr):
    """Test that function raises an error containing expected substring."""
    try:
        func()
        print(f"  ✗ {name}: Expected error but none raised")
        return False
    except Exception as e:
        if expected_error_substr in str(e):
            print(f"  ✓ {name}")
            return True
        else:
            print(f"  ✗ {name}: Wrong error message")
            print(f"      Expected substring: {expected_error_substr}")
            print(f"      Actual error: {e}")
            return False


def run_tests():
    """Run all tests."""
    passed = 0
    failed = 0
    
    print("\n" + "="*60)
    print("Testing replace_el_plus_role_pattern function")
    print("="*60)
    
    # ===== Case 1: (some <-r1-r2...-rn+t> C1) =====
    print("\n--- Case 1: Chain with target (-r1-r2+t) ---")
    
    result, ph = replace_el_plus_role_pattern("(some <-r1+t> <A>)")
    if test_eq("single chain role with target - result", result, "(some <t> <A>)"): passed += 1
    else: failed += 1
    if test_eq("single chain role with target - placeholder", ph, "(some <r1> X)"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2+t> <A>)")
    if test_eq("two chain roles with target - result", result, "(some <t> <A>)"): passed += 1
    else: failed += 1
    if test_eq("two chain roles with target - placeholder", ph, "(some <r1> (some <r2> X))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2-r3+t> <A>)")
    if test_eq("three chain roles with target - result", result, "(some <t> <A>)"): passed += 1
    else: failed += 1
    if test_eq("three chain roles with target - placeholder", ph, "(some <r1> (some <r2> (some <r3> X)))"): passed += 1
    else: failed += 1
    
    # ===== Case 2: (some <-r1-r2...-rn> C1) =====
    print("\n--- Case 2: Chain without target (-r1-r2) ---")
    
    result, ph = replace_el_plus_role_pattern("(some <-r1> <A>)")
    if test_eq("single chain role - result", result, "(some <r1> <A>)"): passed += 1
    else: failed += 1
    if test_eq("single chain role - placeholder", ph, ""): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2> <A>)")
    if test_eq("two chain roles - result", result, "(some <r1> (some <r2> <A>))"): passed += 1
    else: failed += 1
    if test_eq("two chain roles - placeholder", ph, ""): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2-r3> <A>)")
    if test_eq("three chain roles - result", result, "(some <r1> (some <r2> (some <r3> <A>)))"): passed += 1
    else: failed += 1
    
    # ===== Case 3: (some <+t> C1) =====
    print("\n--- Case 3: Plus only (+t) ---")
    
    result, ph = replace_el_plus_role_pattern("(some <+t> <A>)")
    if test_eq("simple plus role - result", result, "(some <t> <A>)"): passed += 1
    else: failed += 1
    if test_eq("simple plus role - placeholder", ph, ""): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <+t> (some <s> <A>))")
    if test_eq("plus role with nested some - result", result, "(some <t> (some <s> <A>))"): passed += 1
    else: failed += 1
    
    # ===== Case 4: Regular expressions =====
    print("\n--- Case 4: Regular expressions (no change) ---")
    
    result, ph = replace_el_plus_role_pattern("<A>")
    if test_eq("atomic concept", result, "<A>"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <r> <A>)")
    if test_eq("regular some", result, "(some <r> <A>)"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <r1> (some <r2> <A>))")
    if test_eq("nested regular some", result, "(some <r1> (some <r2> <A>))"): passed += 1
    else: failed += 1
    
    # ===== And conjunctions =====
    print("\n--- And conjunctions ---")
    
    result, ph = replace_el_plus_role_pattern("(and <A> <B>)")
    if test_eq("simple and", result, "(and <A> <B>)"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(and <A> (some <-r1-r2> <B>))")
    if test_eq("and with case2", result, "(and <A> (some <r1> (some <r2> <B>)))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(and <A> (some <+t> <B>))")
    if test_eq("and with case3", result, "(and <A> (some <t> <B>))"): passed += 1
    else: failed += 1
    
    # ===== Mode constraints =====
    print("\n--- Mode constraints ---")
    
    if test_raises("case2 after case1 raises error",
                   lambda: replace_el_plus_role_pattern("(some <-r+t> (some <-s1-s2> <A>))"),
                   "Case 2 pattern found after Case 1"):
        passed += 1
    else:
        failed += 1
    
    if test_raises("case3 after case2 raises error",
                   lambda: replace_el_plus_role_pattern("(some <-r1-r2> (some <+t> <A>))"),
                   "Case 3 pattern found after Case 2"):
        passed += 1
    else:
        failed += 1
    
    if test_raises("case1 nested raises error",
                   lambda: replace_el_plus_role_pattern("(some <-r+t> (some <-s+u> <A>))"),
                   "Case 1 pattern found in non-initial mode"):
        passed += 1
    else:
        failed += 1
    
    # Valid combinations
    result, ph = replace_el_plus_role_pattern("(some <-r+t> (some <+s> <A>))")
    if test_eq("case3 after case1 is valid", result, "(some <t> (some <s> <A>))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r+t> (some <s> <A>))")
    if test_eq("case4 after case1 is valid", result, "(some <t> (some <s> <A>))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1> (some <-s1-s2> <A>))")
    if test_eq("case2 after case2 is valid", result, "(some <r1> (some <s1> (some <s2> <A>)))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2> (some <s> <A>))")
    if test_eq("case4 after case2 is valid", result, "(some <r1> (some <r2> (some <s> <A>)))"): passed += 1
    else: failed += 1
    
    # ===== Complex expressions =====
    print("\n--- Complex expressions ---")
    
    result, ph = replace_el_plus_role_pattern("(some <-r1> (some <-r2> (some <-r3> <A>)))")
    if test_eq("deeply nested case2", result, "(some <r1> (some <r2> (some <r3> <A>)))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <r> (and <A> <B>))")
    if test_eq("and inside some", result, "(some <r> (and <A> <B>))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-r1-r2> (and <A> <B>))")
    if test_eq("case2 with and inner", result, "(some <r1> (some <r2> (and <A> <B>)))"): passed += 1
    else: failed += 1
    
    # ===== Real-world patterns =====
    print("\n--- Real-world patterns ---")
    
    result, ph = replace_el_plus_role_pattern("(some <-hasParent-hasSibling+hasUncle> <Person>)")
    if test_eq("G path pattern - result", result, "(some <hasUncle> <Person>)"): passed += 1
    else: failed += 1
    if test_eq("G path pattern - placeholder", ph, "(some <hasParent> (some <hasSibling> X))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-hasParent-hasSibling> <Person>)")
    if test_eq("H path pattern", result, "(some <hasParent> (some <hasSibling> <Person>))"): passed += 1
    else: failed += 1
    
    # ===== Edge cases =====
    print("\n--- Edge cases ---")
    
    result, ph = replace_el_plus_role_pattern("")
    if test_eq("empty string", result, ""): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("  (some <-r1-r2> <A>)  ")
    if test_eq("whitespace handling", result, "(some <r1> (some <r2> <A>))"): passed += 1
    else: failed += 1
    
    result, ph = replace_el_plus_role_pattern("(some <-role1-role2+target3> <Concept4>)")
    if test_eq("role names with numbers - result", result, "(some <target3> <Concept4>)"): passed += 1
    else: failed += 1
    
    # ===== Return value structure =====
    print("\n--- Return value structure ---")
    
    ret = replace_el_plus_role_pattern("<A>")
    if test("returns tuple", isinstance(ret, tuple) and len(ret) == 2): passed += 1
    else: failed += 1
    
    _, ph1 = replace_el_plus_role_pattern("(some <-r+t> <A>)")
    _, ph2 = replace_el_plus_role_pattern("(some <-r1-r2> <A>)")
    _, ph3 = replace_el_plus_role_pattern("(some <+t> <A>)")
    _, ph4 = replace_el_plus_role_pattern("(some <r> <A>)")
    if test("placeholder only for case1", ph1 != "" and ph2 == "" and ph3 == "" and ph4 == ""): passed += 1
    else: failed += 1
    
    # ===== Summary =====
    print("\n" + "="*60)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("="*60)
    
    return failed == 0


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
