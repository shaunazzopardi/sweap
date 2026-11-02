from unittest import TestCase
from pathlib import Path
from unittest.mock import patch

from config import Config
from parsing.string_to_ltl import string_to_ltl_with_predicates
from parsing.string_to_program import string_to_program
import parsing.string_to_program as string_to_program_module
import programs.program as program_module
from synthesis.synthesis import process_specifications


class TestProcessSpecifications(TestCase):
    class _SequentialPool:
        def __init__(self, *_args, **_kwargs):
            pass

        def __enter__(self):
            return self

        def __exit__(self, _exc_type, _exc, _tb):
            return False

        def map(self, fn, iterable):
            return [fn(x) for x in iterable]

    def setUp(self):
        self.conf = Config.getConfig()
        self.addCleanup(setattr, self.conf, "dual", self.conf.dual)
        test_prog = (
            Path(__file__).resolve().parent.parent / "test-problems" / "program2.prog"
        )
        with open(test_prog) as program_file:
            with patch.object(string_to_program_module, "Pool", self._SequentialPool):
                with patch.object(program_module, "Pool", self._SequentialPool):
                    self.program, _ = string_to_program(program_file.read())

        # Top-level implication so assumptions/guarantees split is observable.
        self.ltl = string_to_ltl_with_predicates("G(request) -> G(grant)")

    def test_dual_keeps_split_and_shifts_event_references(self):
        self.conf.dual = True

        assumptions, guarantees, _, _ = process_specifications(
            self.program, self.ltl, None
        )

        self.assertEqual(assumptions, [string_to_ltl_with_predicates("G(X(request))")])
        self.assertEqual(guarantees, [string_to_ltl_with_predicates("G(X(grant))")])

    def test_normal_mode_keeps_split_and_original_event_timing(self):
        self.conf.dual = False

        assumptions, guarantees, _, _ = process_specifications(
            self.program, self.ltl, None
        )

        self.assertEqual(assumptions, [string_to_ltl_with_predicates("G(request)")])
        self.assertEqual(guarantees, [string_to_ltl_with_predicates("G(grant)")])
