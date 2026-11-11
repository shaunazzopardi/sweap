import os
from pathlib import Path
from unittest import TestCase, skipUnless
from unittest.mock import patch

import config
from analysis.compatibility_checking.program_to_nuxmv import (
    create_nuxmv_model,
    program_to_nuxmv_model,
)
from analysis.model_checker import ModelChecker, nuxmv_path
from parsing.string_to_program import string_to_program
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.util import conjunct, neg, sat


EXAMPLES = Path(__file__).resolve().parents[1] / "test-problems/history-predicates"


class _SequentialPool:
    def __init__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def map(self, fn, items):
        return [fn(item) for item in items]


class TestHistorySpecExamples(TestCase):
    def setUp(self):
        conf = config.Config.getConfig()
        old_dual = conf.dual
        conf.dual = False
        self.addCleanup(setattr, conf, "dual", old_dual)

    @staticmethod
    def _load(name):
        with (
            patch("parsing.string_to_program.Pool", _SequentialPool),
            patch("programs.program.Pool", _SequentialPool),
            patch("programs.util.run_with_timeout", return_value=(False, None)),
        ):
            return string_to_program((EXAMPLES / name).read_text())

    @skipUnless(os.access(nuxmv_path, os.X_OK), "nuXmv binary is required")
    def test_control_free_spec_verdicts(self):
        expected = {
            # Increment crosses a history threshold; reset and copy need
            # two steps before their updated values appear in history.
            "increment-real.prog": True,
            "reset-real.prog": True,
            "copy-difference-real.prog": True,
            # An initial x != 0 defeats this objective under identity updates.
            "stutter-unreal.prog": False,
            # The mixed predicate is directly implied by the transition.
            "mixed-control-real.prog": True,
            "preview-name-real.prog": True,
        }
        for name, verdict in expected.items():
            with self.subTest(spec=name):
                program, spec = self._load(name)
                self.assertFalse(program.env_events)
                self.assertFalse(program.con_events)
                model = create_nuxmv_model(program_to_nuxmv_model(program))
                actual, output = ModelChecker().invar_check(
                    model, str(spec), 20, True
                )
                self.assertIn("is true" if verdict else "is false", output)
                self.assertEqual(verdict, actual, output)

    def test_parity_game_is_unrealizable(self):
        program, _ = self._load("parity-unreal.prog")
        self.assertEqual("0", str(program.init_var_values["x"]))
        self.assertEqual("1", str(program.init_var_values["y"]))
        # Initially x-y is odd. Each transition changes it by an even
        # amount, so no controller can reach equality. X skips free history.
        even_change = string_to_prop(
            "((x - y) - (x_prev - y_prev) = -2) | "
            "((x - y) - (x_prev - y_prev) = 0) | "
            "((x - y) - (x_prev - y_prev) = 2)"
        )
        for transition in program.transitions:
            self.assertFalse(
                sat(
                    conjunct(transition.formula(), neg(even_change)),
                    program.symbol_table,
                ),
                str(transition),
            )
