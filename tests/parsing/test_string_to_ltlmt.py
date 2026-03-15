from unittest import TestCase

from parsing.string_to_ltl import string_to_ltl_with_predicates
from prop_lang.util import extract_global_formula
from prop_lang.util import conjunct, disjunct, propagate_negations, neg
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_extract_global_formula_value(self):
        formula = string_to_ltl_with_predicates("true")
        result = extract_global_formula(formula)
        self.assertFalse(result)

    def test_extract_global_formula_simple(self):
        formula = string_to_ltl_with_predicates("G a")
        result = extract_global_formula(formula)
        self.assertEqual(result, Variable("a"))

    def test_extract_global_formula_negated_eventually(self):
        formula = string_to_ltl_with_predicates("!(F(!a))")
        result = extract_global_formula(formula)
        self.assertEqual(result, Variable("a"))

    def test_extract_global_formula_conjunction(self):
        formula = string_to_ltl_with_predicates("(G a) && (G b)")
        result = extract_global_formula(formula)
        self.assertEqual(result, conjunct(Variable("a"), Variable("b")))

    def test_extract_global_formula_disjunction(self):
        formula = string_to_ltl_with_predicates("(G a) || (G b)")
        result = extract_global_formula(formula)
        self.assertEqual(result, disjunct(Variable("a"), Variable("b")))

    def test_extract_global_formula_temporal_inner(self):
        formula = string_to_ltl_with_predicates("G (F a)")
        result = extract_global_formula(formula)
        self.assertIsNone(result)

    def test_extract_global_formula_nested_global(self):
        formula = string_to_ltl_with_predicates("G (G a)")
        result = extract_global_formula(formula)
        self.assertEqual(result, Variable("a"))

    def test_extract_global_formula_until(self):
        formula = string_to_ltl_with_predicates("G (a U b)")
        result = extract_global_formula(formula)
        self.assertIsNone(result)

    def test_extract_global_formula_next(self):
        formula = string_to_ltl_with_predicates("G (X a)")
        result = extract_global_formula(formula)
        self.assertIsNone(result)

    def test_extract_global_formula_prop_logic(self):
        formula = string_to_ltl_with_predicates("G ((a && !b) || c)")
        result = extract_global_formula(formula)
        expected = string_to_ltl_with_predicates("(a && !b) || c")
        self.assertEqual(result, expected)

    def test_extract_global_formula_lia(self):
        formula = string_to_ltl_with_predicates("G (a + 1 <= b)")
        result = extract_global_formula(formula)
        expected = string_to_ltl_with_predicates("a + 1 <= b")
        self.assertEqual(result, expected)

    def test_extract_global_formula_negated_eventually_complex(self):
        formula = string_to_ltl_with_predicates("!F(!(a && b))")
        formula = propagate_negations(formula)
        result = extract_global_formula(formula)
        expected = conjunct(Variable("a"), Variable("b"))
        self.assertEqual(result, expected)

    def test_extract_global_formula_negated_eventually_complex2(self):
        formula = string_to_ltl_with_predicates("!F((a && b))")
        formula = propagate_negations(formula)
        result = extract_global_formula(formula)
        expected = disjunct(neg(Variable("a")), neg(Variable("b")))
        self.assertEqual(result, expected)

    def test_extract_global_formula_disjunction_mixed(self):
        formula = string_to_ltl_with_predicates("(G a) || !(F(!b))")
        formula = propagate_negations(formula)
        result = extract_global_formula(formula)
        expected = disjunct(Variable("a"), Variable("b"))
        self.assertEqual(result, expected)
