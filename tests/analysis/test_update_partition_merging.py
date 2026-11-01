from itertools import permutations
from pathlib import Path
from unittest import TestCase
from unittest.mock import patch

import config
from analysis.abstraction.effects_abstraction.abs_util import merge_overlapping_update_parts
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from parsing.string_to_program import string_to_program
from synthesis.synthesis import extract_init_preds, process_specifications


class _SequentialPool:
    def __init__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def map(self, fn, items):
        return [fn(item) for item in items]


class TestUpdatePartitionMerging(TestCase):
    def test_transitive_groups_and_provenance_are_order_independent(self):
        original = {
            frozenset("ab"): {"A", "B"},
            frozenset("bc"): {"B", "C"},
            frozenset("cd"): {"C", "D"},
            frozenset("ef"): {"E", "F"},
            frozenset("fg"): {"F", "G"},
        }
        expected = {
            frozenset("abcd"): {"A", "B", "C", "D"},
            frozenset("efg"): {"E", "F", "G"},
        }
        snapshot = {part: set(old) for part, old in original.items()}
        for order in permutations(original):
            with self.subTest(order=order):
                self.assertEqual(
                    expected,
                    merge_overlapping_update_parts({part: original[part] for part in order}),
                )
        self.assertEqual(snapshot, original)

    def test_empty_and_disjoint_groups_are_unchanged(self):
        self.assertEqual({}, merge_overlapping_update_parts({}))
        parts = {frozenset("ab"): {"P"}, frozenset("cd"): {"Q"}}
        self.assertEqual(parts, merge_overlapping_update_parts(parts))

    def test_copy_chain_spec_builds_disjoint_abstraction_partitions(self):
        conf = config.Config.getConfig()
        old_debug, old_dual = conf.debug, conf.dual
        conf.debug = True
        conf.dual = False
        self.addCleanup(setattr, conf, "debug", old_debug)
        self.addCleanup(setattr, conf, "dual", old_dual)
        spec_path = Path(__file__).resolve().parents[1] / "test-problems/copy-partition-crash.prog"
        with (
            patch("parsing.string_to_program.Pool", _SequentialPool),
            patch("programs.program.Pool", _SequentialPool),
            patch("programs.util.run_with_timeout", return_value=(False, None)),
        ):
            program, spec = string_to_program(spec_path.read_text())
        assumptions, guarantees, _, _ = process_specifications(program, spec, None)
        preds, _, _, signatures, renames = extract_init_preds(program, assumptions, guarantees)
        abstraction = EffectsAbstraction(program, renames)
        with patch(
            "analysis.abstraction.effects_abstraction.effects_abstraction.Pool", _SequentialPool
        ):
            abstraction.add_predicates(preds, set(), signatures, parallelise=False)
        for effects in abstraction.abstract_effect.values():
            groups = {frozenset(str(u.left) for u in part) for part in effects}
            self.assertEqual({frozenset("abcdef"), frozenset("ghi")}, groups)
