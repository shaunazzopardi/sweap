from unittest import TestCase
from unittest.mock import patch

from programs.program import Program, fill_in_minigames
from programs.transition import Transition
from programs import util as program_util_module
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestFillInMinigamesBoolNondet(TestCase):
    def setUp(self):
        self._patcher = patch.object(
            program_util_module,
            "run_with_timeout",
            lambda fn, args, timeout=0.2: (False, None),
        )
        self._patcher.start()

    def tearDown(self):
        self._patcher.stop()

    @staticmethod
    def _build_program(controller_props: list[str]) -> Program:
        b1 = Variable("b1")
        b2 = Variable("b2")
        g = Variable("g")
        transitions = [
            Transition(
                "s0",
                g,
                [Update(b1, NonDeterministic()), Update(b2, NonDeterministic())],
                [],
                "s0",
            )
        ]
        con_events = [(Variable(name), BOOLEAN) for name in controller_props]
        return Program(
            name="bool_nondet_prog",
            sts=["s0"],
            init_st="s0",
            init_values=[
                ("b1", BOOLEAN, Value(BoolAtoms.FALSE)),
                ("b2", BOOLEAN, Value(BoolAtoms.FALSE)),
            ],
            transitions=transitions,
            env_events=[],
            con_events=con_events,
            preprocess=False,
        )

    @staticmethod
    def _extract_rewrite_rhs_names(program: Program):
        rewrites = []
        for t in program.transitions:
            act_map = {str(a.left): a.right for a in t.action}
            if "b1" not in act_map or "b2" not in act_map:
                continue
            r1 = act_map["b1"]
            r2 = act_map["b2"]
            if (
                isinstance(r1, Variable)
                and isinstance(r2, Variable)
                and str(r1) != "b1"
                and str(r2) != "b2"
            ):
                rewrites.append((str(r1), str(r2), str(t.condition)))
        return rewrites

    def test_bool_nondet_updates_reuse_existing_free_controller_props(self):
        prog = self._build_program(["g", "obj", "c1", "c2"])
        new_prog, minigame_states = fill_in_minigames(
            prog, [Variable("obj"), Variable("b1"), Variable("b2")], []
        )

        self.assertEqual(minigame_states, [])
        self.assertFalse(any("_minigame_" in s for s in new_prog.states))

        rewrites = self._extract_rewrite_rhs_names(new_prog)
        self.assertTrue(rewrites)
        rhs1, rhs2, _cond = rewrites[0]
        self.assertNotEqual(rhs1, rhs2)
        self.assertNotIn(rhs1, {"g", "obj"})
        self.assertNotIn(rhs2, {"g", "obj"})
        self.assertTrue({rhs1, rhs2}.issubset({"c1", "c2"}))

    def test_bool_nondet_updates_add_only_required_fresh_controller_props(self):
        prog = self._build_program(["g", "obj", "c1"])
        new_prog, minigame_states = fill_in_minigames(
            prog, [Variable("obj"), Variable("b1"), Variable("b2")], []
        )

        self.assertEqual(minigame_states, [])
        self.assertFalse(any("_minigame_" in s for s in new_prog.states))

        rewrites = self._extract_rewrite_rhs_names(new_prog)
        self.assertTrue(rewrites)
        rhs1, rhs2, _cond = rewrites[0]
        self.assertNotEqual(rhs1, rhs2)
        self.assertNotIn(rhs1, {"g", "obj"})
        self.assertNotIn(rhs2, {"g", "obj"})

        con_names = {str(v) for v, _ in new_prog.con_events}
        fresh = {n for n in con_names if n.startswith("minigame_bool_event_")}
        self.assertEqual(len(fresh), 1)
        self.assertIn("c1", {rhs1, rhs2})

    def test_numeric_neq_pred_upgrade_does_not_crash(self):
        x = Variable("x")
        t = Transition(
            "s0",
            true(),
            [Update(x, NonDeterministic())],
            [],
            "s0",
        )
        t.pred_upgrades = [BiOp(Variable("x'"), "!=", Value("0"))]

        with patch.object(Program, "refine_var_types", lambda self: False):
            program = Program(
                name="neq_pred_upgrade_prog",
                sts=["s0"],
                init_st="s0",
                init_values=[("x", INTEGER, Value("0"))],
                transitions=[t],
                env_events=[],
                con_events=[],
                preprocess=False,
                emit_state_binary_map=False,
            )

        new_prog, _minigame_states = fill_in_minigames(program, [true()], [])
        self.assertGreater(len(new_prog.transitions), 0)
