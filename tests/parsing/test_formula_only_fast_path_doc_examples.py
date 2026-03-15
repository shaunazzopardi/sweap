import unittest
from unittest.mock import patch

from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module
from prop_lang import util as prop_util_module


def _updates_by_name(transition):
    return {str(u.left): str(u.right) for u in transition.action}


class TestFormulaOnlyFastPathDocExamples(unittest.TestCase):
    def setUp(self):
        self._patchers = [
            patch.object(
                program_util_module,
                "run_with_timeout",
                lambda fn, args, timeout=0.2: (False, None),
            ),
            patch.object(
                prop_util_module,
                "run_with_timeout",
                lambda fn, args, timeout=0.2: (False, None),
            ),
        ]
        for p in self._patchers:
            p.start()

    def tearDown(self):
        for p in reversed(self._patchers):
            p.stop()

    def test_doc_example_transition_fragment(self):
        issy = """
        state int x
        state int mode

        formula {
          assert G (([mode = 0]) -> ([x' = x + 1]))
          assert G (([mode = 1]) -> ([x' = x - 1]))
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "doc_example_transition_fragment.issy"
        )

        eval_transitions = [t for t in program.orig_ts if str(t.src) == "eval"]
        self.assertTrue(
            any(
                "(mode = 0)" in str(t.condition)
                and _updates_by_name(t).get("x") in {"(1 + x)", "(x + 1)"}
                for t in eval_transitions
            )
        )
        self.assertTrue(
            any(
                "(mode = 1)" in str(t.condition)
                and _updates_by_name(t).get("x") in {"(x + -1)", "(-1 + x)"}
                for t in eval_transitions
            )
        )
        con_event_names = {str(v.name) for v, _ in program.con_events}
        self.assertFalse(any(n.startswith("formula_con_act_") for n in con_event_names))
        self.assertFalse(any(n.startswith("eq_con_formula_") for n in con_event_names))

    def test_doc_example_explicit_choice(self):
        issy = """
        state int x
        state int m

        formula {
          assert G ((([x' = x + 1] && [m = 0]) || ([x' = x + 2] && [m = 1]) || ([x' = x] && [m = 2])))
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "doc_example_explicit_choice.issy"
        )

        con_event_names = {str(v.name) for v, _ in program.con_events}
        self.assertTrue(any(n.startswith("eq_con_formula_") for n in con_event_names))
        self.assertFalse(any(n.startswith("formula_con_act_") for n in con_event_names))
        self.assertFalse(any(s.startswith("c_") for s in program.states))

    def test_doc_example_partition_chain(self):
        issy = """
        state int x
        state int m

        formula {
          assert G ((([x' = x + 1] && [m = 0]) || ([x' > x] && [m = 1]) || ([x' = x] && [m = 2])))
          assert F [x > 10]
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "doc_example_partition_chain.issy"
        )

        con_event_names = {str(v.name) for v, _ in program.con_events}
        self.assertTrue(any(s.startswith("c_") for s in program.states))
        self.assertTrue(any(n.startswith("formula_con_act_") for n in con_event_names))

    def test_doc_example_final_fallback(self):
        issy = """
        state int x
        state int y

        formula {
          assert G [x' >= x]
          assert G [x' <= x + y]
          assert F [x > 100]
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "doc_example_final_fallback.issy"
        )

        con_event_names = {str(v.name) for v, _ in program.con_events}
        self.assertFalse(any(s.startswith("c_") for s in program.states))
        self.assertFalse(any(n.startswith("formula_con_act_") for n in con_event_names))
        self.assertFalse(any(n.startswith("eq_con_formula_") for n in con_event_names))
        self.assertTrue(any(n.startswith("minigame_event_") for n in con_event_names))

        eval_transitions = [t for t in program.orig_ts if str(t.src) == "eval"]
        self.assertEqual(len(eval_transitions), 1)
        self.assertEqual(str(eval_transitions[0].condition), "TRUE")


if __name__ == "__main__":
    unittest.main()
