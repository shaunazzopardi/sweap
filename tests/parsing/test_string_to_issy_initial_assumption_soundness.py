import unittest
from unittest.mock import patch

from parsing import string_to_issy as string_to_issy_module
from parsing.string_to_ltl import string_to_issy_ltl
from programs import program as program_module
from prop_lang.types.types import INTEGER
from prop_lang.util import extract_initial_values
from prop_lang.variable import Variable


class TestIssyInitialAssumptionExtractionAndStripping(unittest.TestCase):
    def test_extract_formula_only_initial_assumptions_from_implication_antecedent(self):
        formula = string_to_issy_ltl(
            "(((x0 = 0) & (x1 = 0) & (x2 = 0)) -> G((x0 > -1)))"
        )
        extracted = string_to_issy_module.extract_formula_only_initial_assumptions(
            formula
        )
        self.assertEqual(str(extracted), "((x0 = 0) & (x1 = 0) & (x2 = 0))")

    def test_extracted_initial_assumptions_imply_fixed_values(self):
        formula = string_to_issy_ltl(
            "(((x0 = 0) & (x1 = 0) & (x2 = 0)) -> G((x0 > -1)))"
        )
        extracted = string_to_issy_module.extract_formula_only_initial_assumptions(
            formula
        )
        _, fixed = extract_initial_values(
            {Variable("x0"), Variable("x1"), Variable("x2")},
            extracted,
            {"x0": INTEGER, "x1": INTEGER, "x2": INTEGER},
        )
        self.assertEqual(str(fixed[Variable("x0")]), "0")
        self.assertEqual(str(fixed[Variable("x1")]), "0")
        self.assertEqual(str(fixed[Variable("x2")]), "0")

    def test_strip_consumed_initial_assumptions_removes_plain_init_antecedent(self):
        formula = string_to_issy_ltl("((x0 = 0) -> G((x0 > -1)))")
        enforced = string_to_issy_ltl("(x0 = 0)")
        rewritten, removed = (
            string_to_issy_module.strip_consumed_initial_assumptions_from_objectives(
                [formula], enforced, {"x0": INTEGER}
            )
        )
        self.assertEqual(removed, 1)
        self.assertEqual(str(rewritten[0]), "G((x0 > -1))")

    def test_strip_should_not_remove_input_only_initial_assumption(self):
        formula = string_to_issy_ltl("((i = 0) -> G((x0 > -1)))")
        enforced = string_to_issy_ltl("(x0 = 0)")
        rewritten, removed = (
            string_to_issy_module.strip_consumed_initial_assumptions_from_objectives(
                [formula], enforced, {"x0": INTEGER, "i": INTEGER}
            )
        )
        self.assertEqual(removed, 0)
        self.assertEqual(str(rewritten[0]), str(formula))

    def test_strip_should_not_remove_non_unique_state_initial_assumption(self):
        formula = string_to_issy_ltl("(((x0 = 0) | (x0 = 1)) -> G((x0 > -1)))")
        enforced = string_to_issy_ltl("(x0 = 0)")
        rewritten, removed = (
            string_to_issy_module.strip_consumed_initial_assumptions_from_objectives(
                [formula], enforced, {"x0": INTEGER}
            )
        )
        self.assertEqual(removed, 1)
        self.assertEqual(str(rewritten[0]), "G((x0 > -1))")

    def test_strip_should_not_remove_inconsistent_antecedent(self):
        formula = string_to_issy_ltl("(((x0 = 0) & (x0 = 1)) -> G((x0 > -1)))")
        enforced = string_to_issy_ltl("(x0 = 0)")
        rewritten, removed = (
            string_to_issy_module.strip_consumed_initial_assumptions_from_objectives(
                [formula], enforced, {"x0": INTEGER}
            )
        )
        self.assertEqual(removed, 0)
        self.assertEqual(str(rewritten[0]), str(formula))

    def test_extract_should_not_project_global_lhs_to_initial_assumption(self):
        formula = string_to_issy_ltl("(G(p) -> G(q))")
        extracted = string_to_issy_module.extract_formula_only_initial_assumptions(
            formula
        )
        self.assertIsNone(extracted)

    def test_extract_common_initial_assumptions_intersection(self):
        f1 = string_to_issy_ltl("(((x = 0) & (y = 1)) -> G((x > -1)))")
        f2 = string_to_issy_ltl("(((x = 0) & (z = 2)) -> G((x > -1)))")
        extracted = (
            string_to_issy_module.extract_common_formula_only_initial_assumptions(
                [f1, f2]
            )
        )
        self.assertEqual(str(extracted), "(x = 0)")

    def test_strip_must_not_remove_nested_global_implication_antecedent(self):
        formula = string_to_issy_ltl("G(((x = 0) -> X((y = 1))))")
        enforced = string_to_issy_ltl("(x = 0)")
        rewritten, removed = (
            string_to_issy_module.strip_consumed_initial_assumptions_from_objectives(
                [formula], enforced, {"x": INTEGER, "y": INTEGER}
            )
        )
        self.assertEqual(removed, 0)
        self.assertEqual(str(rewritten[0]), str(formula))

    def test_guarantee_extraction_gate_rejects_disjoint_initial_antecedents(self):
        # If different objectives have different initial-only antecedents, there is
        # no single jointly-enforced initial assumption context. Allowing guarantee
        # extraction in this case can strengthen behavior unsoundly.
        f1 = string_to_issy_ltl("((x = 0) -> G(X(r0)))")
        f2 = string_to_issy_ltl("((x = 1) -> G(X(r1)))")
        common = string_to_issy_module.extract_common_formula_only_initial_assumptions(
            [f1, f2]
        )
        self.assertIsNone(common)
        self.assertFalse(
            string_to_issy_module.formula_only_assumptions_are_initial_or_none([f1, f2])
        )

    def test_process_uses_common_init_extraction_for_multiple_original_objectives(self):
        f1 = string_to_issy_ltl("((x = 0) -> G((x > -1)))")
        f2 = string_to_issy_ltl("((x = 0) -> G((x > -1)))")
        with (
            patch.object(
                string_to_issy_module,
                "_build_process_context",
                return_value=([], [Variable("x")], {}, [f1, f2], {"x": INTEGER}),
            ),
            patch.object(
                string_to_issy_module,
                "_finalize_program_initial_values",
                side_effect=RuntimeError("stop_after_gate"),
            ),
            patch.object(
                string_to_issy_module,
                "extract_formula_only_initial_assumptions",
            ) as single_extract_mock,
            patch.object(
                string_to_issy_module,
                "extract_common_formula_only_initial_assumptions",
                return_value=string_to_issy_ltl("(x = 0)"),
            ) as common_extract_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "stop_after_gate"):
                string_to_issy_module.process(
                    "dummy.issy",
                    vars_or_macros=[],
                    formula_objectives=[f1, f2],
                    games=[],
                )
            single_extract_mock.assert_not_called()
            common_extract_mock.assert_called_once()

    def test_process_allows_init_extraction_for_single_original_objective(self):
        f1 = string_to_issy_ltl("((x = 0) -> G((x > -1)))")
        with (
            patch.object(
                string_to_issy_module,
                "_build_process_context",
                return_value=([], [Variable("x")], {}, [f1], {"x": INTEGER}),
            ),
            patch.object(
                string_to_issy_module,
                "_finalize_program_initial_values",
                side_effect=RuntimeError("stop_after_gate"),
            ),
            patch.object(
                string_to_issy_module,
                "extract_formula_only_initial_assumptions",
                return_value=None,
            ) as extract_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "stop_after_gate"):
                string_to_issy_module.process(
                    "dummy.issy",
                    vars_or_macros=[],
                    formula_objectives=[f1],
                    games=[],
                )
            extract_mock.assert_called_once()

    def test_drop_unsat_initial_antecedent_objective_in_multi_objective_set(self):
        f_unsat = string_to_issy_ltl("(((x = 0) & (x = 1)) -> G((x > -1)))")
        f_good = string_to_issy_ltl("((x = 0) -> G((x > -1)))")
        remaining, removed = (
            string_to_issy_module._drop_formula_objectives_with_unsat_initial_antecedents(
                [f_unsat, f_good],
                {"x": INTEGER},
            )
        )
        self.assertEqual(len(removed), 1)
        self.assertEqual(str(removed[0][0]), str(f_unsat))
        self.assertEqual([str(x) for x in remaining], [str(f_good)])

    def test_drop_unsat_initial_antecedent_raises_if_all_objectives_removed(self):
        f1 = string_to_issy_ltl("(((x = 0) & (x = 1)) -> G((x > -1)))")
        f2 = string_to_issy_ltl("(((x = 2) & (x = 3)) -> G((x > -1)))")
        with self.assertRaisesRegex(
            Exception,
            "trivially UNSAT",
        ):
            string_to_issy_module._drop_formula_objectives_with_unsat_initial_antecedents(
                [f1, f2],
                {"x": INTEGER},
            )

    def test_process_formula_only_raises_on_single_unsat_initial_antecedent(self):
        f_unsat = string_to_issy_ltl("(((x = 0) & (x = 1)) -> G((x > -1)))")
        with (
            patch.object(
                string_to_issy_module,
                "_build_process_context",
                return_value=([], [Variable("x")], {}, [f_unsat], {"x": INTEGER}),
            ),
            patch.object(
                string_to_issy_module,
                "_finalize_program_initial_values",
            ) as finalize_mock,
        ):
            with self.assertRaisesRegex(Exception, "trivially UNSAT"):
                string_to_issy_module.process(
                    "dummy.issy",
                    vars_or_macros=[],
                    formula_objectives=[f_unsat],
                    games=[],
                )
            finalize_mock.assert_not_called()


if __name__ == "__main__":
    unittest.main()
