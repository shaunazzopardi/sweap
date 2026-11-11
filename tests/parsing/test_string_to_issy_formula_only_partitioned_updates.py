import unittest
from unittest.mock import patch

from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module


class TestStringToIssyFormulaOnlyPartitionedUpdates(unittest.TestCase):
    def setUp(self):
        self._patchers = [
            patch.object(
                program_util_module,
                "run_with_timeout",
                lambda fn, args, timeout=0.2: (False, None),
            ),
        ]
        for p in self._patchers:
            p.start()

    def tearDown(self):
        for p in reversed(self._patchers):
            p.stop()

    def test_formula_only_single_primed_updates_have_no_legacy_formula_part_artifacts(
        self,
    ):
        issy = """
        state int x
        state int y

        formula {
          assume [x = 0] && [y = 0]
          assert G ([x' = x + 1] && [y' = y + 1])
        }
        """

        program, objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_partitioned_supported.issy"
        )

        self.assertFalse(any(s.startswith("formula_part_") for s in program.states))
        self.assertFalse(any("_minigame_" in s for s in program.states))
        self.assertTrue(
            all(not str(v).startswith("formula_pred_") for v, _ in program.con_events)
        )
        self.assertNotIn("formula_part_", str(objective))

    def test_partition_chain_falls_back_when_update_uses_multiple_primed_vars(self):
        issy = """
        state int x
        state int y

        formula {
          assert G [x' = y']
        }
        """

        program, _objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_partitioned_fallback.issy"
        )

        self.assertFalse(any(s.startswith("c_") for s in program.states))
        self.assertFalse(any(s.startswith("formula_part_") for s in program.states))
        self.assertTrue(any("_minigame_" in s for s in program.states))

    def test_partition_chain_fast_path_allows_two_implication_objectives(self):
        f1 = string_to_issy_module.string_to_issy_ltl("((x = 0) -> G((x' = (x + 1))))")
        f2 = string_to_issy_module.string_to_issy_ltl(
            "((x = 0) -> G((x' = (x + 1 + i))))"
        )

        seen = {}

        def _infer_stub(scan_context):
            seen["formula"] = str(scan_context.objective_for_check)
            raise RuntimeError("stop_after_infer")

        with patch.object(
            string_to_issy_module,
            "_build_process_context",
            return_value=(
                [string_to_issy_module.Variable("i")],
                [string_to_issy_module.Variable("x")],
                {},
                [f1, f2],
                {
                    "i": string_to_issy_module.INTEGER,
                    "x": string_to_issy_module.INTEGER,
                    "x'": string_to_issy_module.INTEGER,
                },
            ),
        ), patch.object(
            string_to_issy_module,
            "infer_spot_update_restrictions",
            side_effect=_infer_stub,
        ):
            with self.assertRaisesRegex(RuntimeError, "stop_after_infer"):
                string_to_issy_module.process(
                    "formula_only_two_implications_fast_path.issy",
                    vars_or_macros=[],
                    formula_objectives=[f1, f2],
                    games=[],
                )

        self.assertIn("(x = 0)", seen.get("formula", ""))
        self.assertIn("->", seen.get("formula", ""))
        self.assertIn("(x' = (x + 1))", seen.get("formula", ""))
        self.assertIn("(x' = (x + 1 + i))", seen.get("formula", ""))

    def test_legacy_formula_part_states_are_never_generated(self):
        issy = """
        state int x

        formula {
          assume [x = 0]
          assert G [x' = x + 2]
        }
        """

        program, _objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_partitioned_non_unit_step.issy"
        )

        self.assertFalse(any(s.startswith("formula_part_") for s in program.states))

    def test_formula_only_initial_assumptions_are_applied_despite_trivial_game_objective(
        self,
    ):
        issy = """
        state int x

        formula {
          assume [x = 0]
          assert G [x' = x + 1]
        }
        """

        program, objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_init_assumptions.issy"
        )

        # Transition-fragment fast path collapses this case to TRUE.
        self.assertEqual(program.init_var_values, {})
        self.assertEqual(str(objective), "TRUE")

    def test_goal_scoped_guarantee_extraction_recovers_partition_chain_fast_path(self):
        issy = """
        state int q
        state int y

        formula {
            assert G (([q > 0] && [y > 0]) ->
                      ([y' = y] && [q' = q - y - 1]))
            assert G (([q > 0] && [y <= 0]) ->
                      ([y' = y] && [q' = q + y - 1]))
            assert F [q <= 0]
        }
        """

        program, _objective = string_to_issy_module.string_to_issy(
            issy, "tacas26-ex-2-05.issy"
        )

        # Goal-scoped guarantees now remain on transition-fragment fast path.
        self.assertEqual(set(program.states), {"eval"})
        self.assertFalse(
            any(e[0].name.startswith("formula_con_act_") for e in program.con_events)
        )

    def test_formula_only_init_extraction_with_internal_minigame_progress_objective(
        self,
    ):
        issy = """
        state int x
        state int y
        state int z
        state int sched

        formula {
          assume [x = 0] && [y = 0] && [z = 0]
          assert G ( ([sched' = 1] -> [y' = y]) & ([sched' = 2] -> [y' = y + 1]) & ([sched' = 3] -> [y' = y - 1]) )
          assert G ([y != 2] | [z != 1])
        }
        """

        program, objective = string_to_issy_module.string_to_issy(
            issy, "test-14-like-init-extraction.issy"
        )

        # With internal minigame progress objective, init assumptions remain
        # in the objective antecedent; only helper vars are materialized here.
        self.assertIsNone(program.init_var_values.get("x"))
        self.assertIsNone(program.init_var_values.get("y"))
        self.assertIsNone(program.init_var_values.get("z"))
        self.assertEqual(str(program.init_var_values.get("int_y")), "0")
        self.assertIn("((x = 0) & (y = 0) & (z = 0)) ->", str(objective))


if __name__ == "__main__":
    unittest.main()
