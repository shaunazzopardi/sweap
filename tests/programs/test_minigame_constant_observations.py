from pathlib import Path
from unittest import TestCase
from unittest.mock import patch

import config
from parsing.string_to_issy import string_to_issy
from programs.minigame_filler import MinigameFiller
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestMinigameConstantObservations(TestCase):
    def setUp(self):
        cfg = config.Config.getConfig()
        self.addCleanup(setattr, cfg, "workers", cfg.workers)
        cfg.workers = 1
        patcher = patch("programs.util.run_with_timeout", return_value=(False, None))
        patcher.start()
        self.addCleanup(patcher.stop)

    def profile(self, guard, actions=None):
        x, y = Variable("x"), Variable("y")
        program = Program(
            "observations", ["q"], "q",
            [("x", INTEGER), ("y", INTEGER)],
            [Transition("q", guard, actions or [Update(x, NonDeterministic())], [], "q")],
            [], [], preprocess=False, emit_state_binary_map=False,
        )
        return MinigameFiller(program, [], [])._collect_constant_comparison_profile()

    def test_guard_equality_adds_its_constant(self):
        allowed, constants = self.profile(BiOp(Variable("x"), "=", Value(10)))
        self.assertTrue(allowed["x"])
        self.assertEqual({10}, constants["x"])

    def test_ordered_and_relational_guards_disable_constant_choice(self):
        x = Variable("x")
        for guard in (BiOp(x, ">=", Value(10)), BiOp(x, "=", Variable("y"))):
            allowed, _ = self.profile(guard)
            self.assertFalse(allowed["x"])

    def test_copy_observes_the_actual_numeric_value(self):
        x, y = Variable("x"), Variable("y")
        allowed, _ = self.profile(true(), [Update(x, NonDeterministic()), Update(y, x)])
        self.assertFalse(allowed["x"])

    def test_issy_arena_threshold_keeps_numeric_movement(self):
        source = Path(__file__).parents[1] / "test-problems/issy-arena-threshold-choice.issy"
        program, _ = string_to_issy(source.read_text(), "arena_threshold")
        x = Variable("x")
        numeric_steps = [u for t in program.transitions if t.src == t.tgt
                         for u in t.action if u.left == x and u.right != x
                         and x in u.right.variablesin()]
        self.assertTrue(numeric_steps, "The arena threshold must not collapse x to 0/-1")
