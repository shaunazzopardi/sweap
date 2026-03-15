import unittest
from unittest.mock import patch

from parsing.util.issy.reductions.ltl.guarantee_transition_extractor import (
    IssyGuaranteeTransitionExtractor,
)
from parsing.string_to_ltl import string_to_issy_ltl
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.util import propagate_negations, strip_mathexpr


class TestIssyGuaranteeTransitionExtractor(unittest.TestCase):
    def setUp(self):
        self.symbol_table = {
            "i": INTEGER,
            "x": INTEGER,
            "y": INTEGER,
            "z": INTEGER,
            "x'": INTEGER,
            "y'": INTEGER,
            "r0": BOOLEAN,
            "r1": BOOLEAN,
            "r0'": BOOLEAN,
            "r1'": BOOLEAN,
        }

    @staticmethod
    def _prepared_objective(formula_text: str):
        return strip_mathexpr(propagate_negations(string_to_issy_ltl(formula_text)))

    def test_extracts_only_from_guarantee_side(self):
        formula = self._prepared_objective(
            "((i = 0) -> (G((x' = (x + 1))) & G((z > 0))))"
        )
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y"},
            eval_state="eval",
        )

        result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertEqual(result.extracted_rule_count, 1)
        self.assertEqual(result.extracted_formula_count, 1)
        self.assertEqual(len(result.transitions), 1)
        self.assertIn("(i = 0)", str(result.rewritten_objectives[0]))
        self.assertIn("G((z > 0))", str(result.rewritten_objectives[0]))

    def test_rejects_conflicting_updates_on_overlapping_guards(self):
        formula = self._prepared_objective(
            "(G(((x = 0) -> (y' = 0))) & G(((x = 0) -> (y' = 1))))"
        )
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y"},
            eval_state="eval",
        )

        result = extractor.extract([formula])

        # Current extractor semantics keep satisfiable non-conflicting regions.
        self.assertTrue(result.applied)
        self.assertIsNone(result.skipped_reason)
        self.assertEqual(len(result.transitions), 1)
        self.assertIn("!(x = 0)", str(result.transitions[0].condition))
        self.assertEqual(len(result.transitions[0].action), 0)
        self.assertEqual(str(result.rewritten_objectives[0]), "TRUE")

    def test_supports_x_style_updates(self):
        formula = self._prepared_objective("G(((x = 0) -> X((y = (x + 1)))))")
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y"},
            eval_state="eval",
        )

        result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertEqual(len(result.transitions), 2)
        rendered = [str(t) for t in result.transitions]
        self.assertTrue(any("(x = 0)" in t and "y := (x + 1)" in t for t in rendered))
        self.assertTrue(any("!(x = 0)" in t for t in rendered))

    def test_next_boolean_constraint_is_extracted_as_update_branches(self):
        formula = self._prepared_objective("G((!r0' | !r1'))")
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y", "r0", "r1"},
            eval_state="eval",
        )

        result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertEqual(len(result.transitions), 3)
        for t in result.transitions:
            self.assertEqual(str(t.condition), "TRUE")
            lhs_updates = {str(u.left) for u in t.action}
            self.assertEqual(lhs_updates, {"r0", "r1"})

    def test_next_boolean_implication_stays_on_update_side(self):
        formula = self._prepared_objective("G((r0' -> (x' = (x + 1))))")
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y", "r0", "r1"},
            eval_state="eval",
        )

        result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertEqual(len(result.transitions), 2)
        for t in result.transitions:
            self.assertEqual(str(t.condition), "TRUE")
            lhs_updates = {str(u.left) for u in t.action}
            self.assertIn("r0", lhs_updates)

    def test_implication_next_boolean_guard_uses_minterm_update_map_expansion(self):
        # This shape is handled in _extract_rules_from_global_guarantee and should
        # call _satisfying_minterm_update_maps for both guard and negated guard.
        formula = self._prepared_objective("G(((r0' | !r1') -> r0'))")
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y", "r0", "r1"},
            eval_state="eval",
        )

        with patch.object(
            extractor,
            "_satisfying_minterm_update_maps",
            wraps=extractor._satisfying_minterm_update_maps,
        ) as minterm_spy:
            result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertGreaterEqual(minterm_spy.call_count, 2)
        self.assertEqual(str(result.rewritten_objectives[0]), "TRUE")

    def test_boolean_primed_transition_formulas_exercise_minterm_update_maps(self):
        cases = [
            ("G(r0')", 1, 1),
            ("G((r0' | r1'))", 3, 1),
            ("G((!r0' | !r1'))", 3, 1),
            ("G(((r0' | !r1') -> r0'))", 3, 2),
            ("G(((r0' & r1') -> r0'))", 4, 2),
        ]

        for formula_text, expected_transitions, min_minterm_calls in cases:
            with self.subTest(formula=formula_text):
                extractor = IssyGuaranteeTransitionExtractor(
                    self.symbol_table,
                    {"x", "y", "r0", "r1"},
                    eval_state="eval",
                )
                formula = self._prepared_objective(formula_text)

                with patch.object(
                    extractor,
                    "_satisfying_minterm_update_maps",
                    wraps=extractor._satisfying_minterm_update_maps,
                ) as minterm_spy:
                    result = extractor.extract([formula])

                self.assertTrue(result.applied)
                self.assertEqual(result.extracted_formula_count, 1)
                self.assertEqual(str(result.rewritten_objectives[0]), "TRUE")
                self.assertEqual(len(result.transitions), expected_transitions)
                self.assertGreaterEqual(minterm_spy.call_count, min_minterm_calls)

                for transition in result.transitions:
                    self.assertEqual(str(transition.condition), "TRUE")
                    lhs_updates = {str(u.left) for u in transition.action}
                    self.assertTrue(lhs_updates.issubset({"r0", "r1"}))

    def test_boolean_guard_implication_with_numeric_and_boolean_updates(self):
        formula = self._prepared_objective(
            "G(((r0' | !r1') -> ((x' = (x + 1)) & r0')))"
        )
        extractor = IssyGuaranteeTransitionExtractor(
            self.symbol_table,
            {"x", "y", "r0", "r1"},
            eval_state="eval",
        )

        with patch.object(
            extractor,
            "_satisfying_minterm_update_maps",
            wraps=extractor._satisfying_minterm_update_maps,
        ) as minterm_spy:
            result = extractor.extract([formula])

        self.assertTrue(result.applied)
        self.assertEqual(result.extracted_formula_count, 1)
        self.assertEqual(str(result.rewritten_objectives[0]), "TRUE")
        self.assertEqual(len(result.transitions), 3)
        self.assertGreaterEqual(minterm_spy.call_count, 2)

        rendered_updates = [set(str(u) for u in t.action) for t in result.transitions]
        # One false-guard branch (only boolean updates)
        self.assertTrue(any("r0 := FALSE" in us and "r1 := TRUE" in us for us in rendered_updates))
        # True-guard branches include numeric + boolean updates
        self.assertTrue(any("x := (x + 1)" in us and "r0 := TRUE" in us for us in rendered_updates))


if __name__ == "__main__":
    unittest.main()
