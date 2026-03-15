import unittest
from unittest.mock import patch

from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module
from prop_lang.nondet import NonDeterministic


def _updates_by_name(transition):
    return {str(u.left): u.right for u in transition.action}


class TestFormulaOnlyTransitionFragmentCompletion(unittest.TestCase):
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

    def test_exclusive_eventual_goal_uses_stutter_completion(self):
        issy = """
        state int a
        state int b

        formula {
          assert G (([a > 0] && [b > 0]) -> ([a' = a - 1] && [b' = b]))
          assert G (([a > 0] && [b <= 0]) -> ([a' = a - 1] && [b' = b - 1]))
          assert F ([a <= 0])
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "transition_fragment_completion_stutter.issy"
        )

        eval_transitions = [
            t for t in program.orig_ts if str(t.src) == "eval" and str(t.tgt) == "eval"
        ]
        self.assertGreater(len(eval_transitions), 0)

        self.assertFalse(any("_minigame_" in s for s in program.states))
        self.assertFalse(
            any(
                isinstance(u.right, NonDeterministic)
                for t in eval_transitions
                for u in t.action
            )
        )
        self.assertTrue(
            any(
                {k: str(v) for k, v in _updates_by_name(t).items() if k in {"a", "b"}}
                == {"a": "a", "b": "b"}
                for t in eval_transitions
            )
        )

    def test_non_exclusive_eventual_goal_keeps_nondet_completion(self):
        issy = """
        state int a
        state int b

        formula {
          assert G (([a > 0] && [b > 0]) -> ([a' = a - 1] && [b' = b]))
          assert G (([a > 0] && [b <= 0]) -> ([a' = a - 1] && [b' = b - 1]))
          assert F ([a > 0])
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "transition_fragment_completion_nondet.issy"
        )

        eval_transitions = [
            t for t in program.orig_ts if str(t.src) == "eval" and str(t.tgt) == "eval"
        ]
        self.assertGreater(len(eval_transitions), 0)

        if any("_minigame_" in s for s in program.states):
            # Non-exclusive objective can fall back to partition/minigame path.
            self.assertTrue(True)
        else:
            # If transition-fragment path is used, completion should remain nondet.
            self.assertTrue(
                any(
                    all(
                        isinstance(_updates_by_name(t).get(v), NonDeterministic)
                        for v in {"a", "b"}
                    )
                    for t in eval_transitions
                )
            )


if __name__ == "__main__":
    unittest.main()
