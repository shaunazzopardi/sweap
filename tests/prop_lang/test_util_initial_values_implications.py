import unittest

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from prop_lang.util import (
    extract_initial_formula,
    extract_initial_values,
    neg,
    normalize_ltl,
    propagate_negations,
)
from prop_lang.types.types import BOOLEAN
from prop_lang.types.values import BoolAtoms
from prop_lang.value import Value


class TestExtractInitialValuesImplications(unittest.TestCase):
    def setUp(self):
        self.a = Variable("a")
        self.b = Variable("b")
        self.c = Variable("c")
        self.symbol_table = {"a": BOOLEAN, "b": BOOLEAN, "c": BOOLEAN}

    def test_implication_with_temporal_antecedent_returns_none(self):
        formula = BiOp(UniOp("G", UniOp("!", self.a)), "->", self.b)
        self.assertIsNone(extract_initial_formula(formula))
        init_formula, fixed = extract_initial_values(
            {self.a, self.b}, formula, self.symbol_table
        )
        self.assertIsNone(init_formula)
        self.assertEqual(fixed, {})

    def test_implication_with_until_antecedent_returns_none(self):
        formula = BiOp(BiOp(self.a, "U", self.b), "->", self.c)
        self.assertIsNone(extract_initial_formula(formula))

    def test_biimplication_with_temporal_side_returns_none(self):
        formula = BiOp(UniOp("G", self.a), "<->", self.b)
        self.assertIsNone(extract_initial_formula(formula))

    def test_biimplication_with_both_global_sides_returns_none(self):
        formula = BiOp(UniOp("G", self.a), "<->", UniOp("G", self.b))
        self.assertIsNone(extract_initial_formula(formula))

    def test_implication_with_initial_antecedent_and_global_consequent_extracts(self):
        formula = BiOp(self.a, "->", UniOp("G", self.b))
        expected = BiOp(self.a, "->", self.b)
        self.assertEqual(extract_initial_formula(formula), expected)

    def test_pure_propositional_implication_is_preserved(self):
        formula = BiOp(self.a, "->", self.b)
        self.assertEqual(extract_initial_formula(formula), formula)

    def test_violation_flow_still_extracts_useful_initial_constraints(self):
        # Objective: if always !a then b must hold now.
        objective = BiOp(UniOp("G", UniOp("!", self.a)), "->", self.b)
        # Violation target used in initialization flow: !(objective).
        violation_formula = normalize_ltl(propagate_negations(neg(objective)))

        init_formula = extract_initial_formula(violation_formula)
        self.assertIsNotNone(init_formula)

        _, fixed = extract_initial_values(
            {self.a, self.b},
            violation_formula,
            self.symbol_table,
        )
        self.assertEqual(fixed[self.a], Value(BoolAtoms.FALSE))
        self.assertEqual(fixed[self.b], Value(BoolAtoms.FALSE))

    def test_conjunction_keeps_extractable_initial_part(self):
        formula = BiOp(BiOp(UniOp("G", UniOp("!", self.a)), "->", self.b), "&", self.c)
        self.assertEqual(extract_initial_formula(formula), self.c)

    def test_disjunction_with_nonextractable_side_returns_none(self):
        formula = BiOp(BiOp(UniOp("G", UniOp("!", self.a)), "->", self.b), "|", self.c)
        self.assertIsNone(extract_initial_formula(formula))

    def test_violation_flow_with_until_antecedent_extracts_initial_projection(self):
        objective = BiOp(BiOp(self.a, "U", self.b), "->", self.c)
        violation_formula = normalize_ltl(propagate_negations(neg(objective)))
        init_formula = extract_initial_formula(violation_formula)
        self.assertIsNotNone(init_formula)
        _, fixed = extract_initial_values(
            {self.a, self.b, self.c},
            violation_formula,
            self.symbol_table,
        )
        self.assertEqual(fixed[self.c], Value(BoolAtoms.FALSE))


if __name__ == "__main__":
    unittest.main()
