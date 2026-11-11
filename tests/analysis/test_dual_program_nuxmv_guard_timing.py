from analysis.compatibility_checking.program_to_nuxmv import program_to_nuxmv_model
import re
import unittest
from pathlib import Path
from unittest.mock import patch

from config import Config
from parsing.string_to_program import string_to_program


class _SeqPool:
    def __init__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        return False

    def map(self, fn, iterable):
        return [fn(item) for item in iterable]


def _run_no_timeout(fn, args, timeout, *extra):
    return True, fn(*args)


def _arbiter_program_text():
    benchmark = (
        Path(__file__).resolve().parents[2]
        / "benchmarks"
        / "sweap"
        / "finite"
        / "arbiter-paper-5.prog"
    )
    return benchmark.read_text()


class TestDualProgramNuXmvGuardTiming(unittest.TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self.old_dual = self.conf.dual
        self.old_workers = self.conf.workers
        self.conf.workers = 1

    def tearDown(self):
        self.conf.dual = self.old_dual
        self.conf.workers = self.old_workers

    def _parse_program(self):
        with patch("parsing.string_to_program.Pool", _SeqPool), patch(
            "programs.program.Pool", _SeqPool
        ), patch("prop_lang.util.run_with_timeout", _run_no_timeout), patch(
            "programs.util.run_with_timeout", _run_no_timeout
        ):
            return string_to_program(_arbiter_program_text())[0]

    def test_dual_program_guards_use_current_controller_events(self):
        self.conf.dual = True
        program = self._parse_program()

        model = program_to_nuxmv_model(program)
        guard_defs = "\n".join(d for d in model.define if d.startswith("guard_"))

        self.assertNotIn("next(grantA)", guard_defs)
        self.assertNotIn("next(grantB)", guard_defs)
        self.assertNotIn("next(finished)", guard_defs)
        self.assertIsNotNone(re.search(r"(?<!next\()grantA\b", guard_defs))
        self.assertIsNotNone(re.search(r"(?<!next\()grantB\b", guard_defs))
        self.assertIsNotNone(re.search(r"(?<!next\()finished\b", guard_defs))

    def test_dual_does_not_swap_program_io_roles(self):
        self.conf.dual = True
        dual_program = self._parse_program()

        self.conf.dual = False
        base_program = self._parse_program()

        dual_env = {str(v) for v, _ in dual_program.env_events}
        base_env = {str(v) for v, _ in base_program.env_events}

        self.assertEqual(dual_env, {"request", "changeRoom"})
        self.assertEqual(base_env, dual_env)


if __name__ == "__main__":
    unittest.main()
