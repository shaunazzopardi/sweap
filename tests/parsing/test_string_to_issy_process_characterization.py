import unittest
from pathlib import Path
from unittest.mock import patch

from pysmt.shortcuts import reset_env

from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module


class TestStringToIssyProcessCharacterization(unittest.TestCase):
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

    @staticmethod
    def _repo_root() -> Path:
        return Path(__file__).resolve().parents[2]

    def _snapshot(self, rel_path: str):
        reset_env()
        path = self._repo_root() / rel_path
        program, objective = string_to_issy_module.string_to_issy(
            path.read_text(), path.name
        )
        return {
            "program": program,
            "objective": objective,
            "states": len(program.states),
            "transitions": len(program.transitions),
            "env_events": len(program.env_events),
            "con_events": len(program.con_events),
            "local_vars": len(program.local_vars),
        }

    def test_process_characterization_games_flow(self):
        observed = self._snapshot("benchmarks/issy/test-01.issy")
        program = observed["program"]
        self.assertEqual(observed["states"], 4)
        self.assertEqual(observed["transitions"], 9)
        self.assertEqual(observed["env_events"], 2)
        self.assertEqual(observed["con_events"], 0)
        self.assertEqual(observed["local_vars"], 4)
        self.assertIn("G(F((active1 & active2)))", str(observed["objective"]))
        self.assertEqual(
            program.states,
            {
                "game_0_state_l0_game_1_state_l0",
                "game_0_state_l0_game_1_state_l1",
                "game_0_state_l1_game_1_state_l0",
                "game_0_state_l1_game_1_state_l1",
            },
        )
        per_src = {}
        for t in program.transitions:
            per_src[t.src] = per_src.get(t.src, 0) + 1
            self.assertEqual(
                {str(a.left) for a in t.action}, {"active1", "active2", "x1", "x2"}
            )
        self.assertEqual(
            per_src,
            {
                "game_0_state_l0_game_1_state_l0": 4,
                "game_0_state_l0_game_1_state_l1": 2,
                "game_0_state_l1_game_1_state_l0": 2,
                "game_0_state_l1_game_1_state_l1": 1,
            },
        )

    def test_process_characterization_formula_only_flow(self):
        observed = self._snapshot("benchmarks/issy/counters/counter-3-7-formula.issy")
        program = observed["program"]
        objective = str(observed["objective"])
        self.assertEqual(observed["states"], 1)
        self.assertGreaterEqual(observed["transitions"], 1)
        self.assertEqual(observed["env_events"], 1)
        self.assertEqual(observed["con_events"], 7)
        self.assertEqual(observed["local_vars"], 3)
        self.assertIn("F((x0 > 7))", objective)
        self.assertIn("(x1 = 7)", objective)
        self.assertIn("(x2 = 7)", objective)
        self.assertEqual(program.states, {"c_x0_x1_x2"})
        self.assertEqual(
            {str(v) for v, _ in program.con_events},
            {
                "d1",
                "d2",
                "formula_con_act_0",
                "formula_con_act_1",
                "formula_con_act_2",
                "formula_con_act_3",
                "formula_con_act_4",
            },
        )
        self.assertTrue(
            any(
                t.src == "c_x0_x1_x2" and t.tgt == "c_x0_x1_x2"
                for t in program.transitions
            )
        )

    def test_buggy2_minigame_uses_unrestricted_encoding(self):
        observed = self._snapshot("benchmarks/issy/buggy2.issy")
        program = observed["program"]

        local_names = {str(v) for v in program.local_vars}
        self.assertIn("int_x", local_names)

        minigame_state = next(s for s in program.states if s.endswith("_minigame_0"))
        src_state = next(s for s in program.states if s.endswith("_state_l1"))

        from_src_to_minigame = [
            t
            for t in program.transitions
            if t.src == src_state and t.tgt == minigame_state
        ]
        self.assertTrue(
            from_src_to_minigame, "Expected transition into minigame state."
        )
        self.assertTrue(
            any(str(a) == "int_x := x" for t in from_src_to_minigame for a in t.action)
        )

        looping = [
            t
            for t in program.transitions
            if t.src == minigame_state and t.tgt == minigame_state
        ]
        self.assertTrue(
            any(str(a) == "int_x := (int_x + 1)" for t in looping for a in t.action)
        )
        self.assertTrue(
            any(str(a) == "int_x := int_x" for t in looping for a in t.action)
        )
        self.assertTrue(
            all(str(a) != "x := (x + -1)" for t in looping for a in t.action)
        )

        exit_to_l1 = [
            t
            for t in program.transitions
            if t.src == minigame_state and t.tgt == src_state
        ]
        self.assertTrue(exit_to_l1, "Expected transition from minigame back to l1.")
        self.assertTrue(any("(int_x < 0)" in str(t.condition) for t in exit_to_l1))
        self.assertTrue(
            any(
                "((int_x + -x) > 0)" in str(t.condition)
                or "(int_x > (0 + x))" in str(t.condition)
                or "(int_x > x)" in str(t.condition)
                for t in exit_to_l1
            )
        )
        self.assertTrue(
            any(str(a) == "x := int_x" for t in exit_to_l1 for a in t.action)
        )


if __name__ == "__main__":
    unittest.main()
