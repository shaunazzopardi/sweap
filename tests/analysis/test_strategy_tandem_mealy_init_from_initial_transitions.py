from unittest import TestCase
from types import SimpleNamespace

from analysis.compatibility_checking.strategy_to_nuxmv import (
    strategy_to_nuxmv_model,
)
from config import Config
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class TestStrategyTandemMealyInitFromInitialTransitions(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual
        self.conf.dual = True

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_dual_mealy_init_uses_initial_transition_effects(self):
        i = Variable("i")
        o = Variable("o")
        machine = MealyMachine("controller", 0, [i], [o])
        machine.states = {"st_0", "st_1", "st_2"}
        machine.transitions = {
            "st_0": {
                "st_1": {(i, o)},
                "st_2": {(UniOp("!", i), UniOp("!", o))},
            }
        }

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [],
            init_choice_logic=i,
        )
        init_cond = model.init[0]
        model_text = "\n".join(model.define + model.trans)

        self.assertNotEqual(init_cond, "strategy_state = st_0")
        self.assertIn("strategy_state = st_1", init_cond)
        self.assertNotIn("o", init_cond)
        self.assertNotIn("strategy_state = st_2", init_cond)
        self.assertNotIn("(i)", init_cond)
        self.assertNotIn("(!(i))", init_cond)
        self.assertNotIn("next(o)", model_text)

    def test_dual_mealy_init_raises_if_qe_projection_is_false(self):
        i = Variable("i")
        o = Variable("o")
        machine = MealyMachine("controller", 0, [i], [o])
        machine.states = {"st_0", "st_1", "st_2"}
        machine.transitions = {
            "st_0": {
                "st_1": {(i, o)},
                "st_2": {(UniOp("!", i), o)},
            }
        }

        with self.assertRaisesRegex(
            Exception,
            "Something wrong in LTL, no valid controller choice for initial state precicates",
        ):
            strategy_to_nuxmv_model(
                machine,
                [],
                [],
                [],
                [],
                init_choice_logic=UniOp("!", o),
            )

    def test_dual_mealy_guards_next_transition_predicates(self):
        i = Variable("i")
        pred_x = Variable("pred__x")
        bin_x = Variable("bin_x")
        tran_pred = Variable("tran_pred")
        q = Variable("q")
        machine = MealyMachine("controller", 0, [i], [pred_x, bin_x, tran_pred, q])
        machine.transitions = {
            "st_0": {
                "st_0": {
                    (i, BiOp(BiOp(BiOp(pred_x, "&", bin_x), "&", tran_pred), "&", q))
                }
            }
        }
        trans_pred = SimpleNamespace(bool_rep={Variable("dummy"): tran_pred})

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [trans_pred],
        )
        guard_0 = next(d for d in model.define if d.startswith("controller_guard_0 :="))

        self.assertIn("next(pred__x)", guard_0)
        self.assertIn("next(bin_x)", guard_0)
        self.assertIn("next(tran_pred)", guard_0)
        self.assertIn(" q", guard_0)
        self.assertNotIn("next(q)", guard_0)

    def test_dual_moore_verification_init_projects_out_bootstrap_props(self):
        i = Variable("env_init_i")
        o = Variable("o")
        machine = MooreMachine("counterstrategy", 0, [i], [o])
        machine.out = {"st_0": BiOp(i, "&", o)}
        machine.transitions = {"st_0": [(o, "st_0")]}

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [],
            for_verification=True,
            init_choice_logic=i,
        )
        init_cond = model.init[0]
        model_text = "\n".join(model.define + model.trans)

        # Single-state strategies omit the redundant state variable.
        self.assertNotIn("strategy_state", init_cond)
        self.assertFalse(any(v.name == "strategy_state" for v in model.vars))
        # The target state output constrains the first actual program step.
        self.assertIn("o", init_cond)
        self.assertNotIn("env_init_i", init_cond)
        self.assertIn("next(o)", model_text)

    def test_dual_moore_verification_init_keeps_current_outputs_and_state(self):
        i = Variable("env_init_i")
        o = Variable("o")
        aux = Variable("env_init_aux")
        bin_keep = Variable("bin_keep")
        q = Variable("q")
        machine = MooreMachine("counterstrategy", 0, [i], [o, aux, bin_keep, q])
        machine.out = {"st_0": BiOp(BiOp(BiOp(o, "&", aux), "&", bin_keep), "&", q)}
        machine.transitions = {
            "st_0": [(BiOp(BiOp(aux, "&", q), "&", bin_keep), "st_0")]
        }

        model = strategy_to_nuxmv_model(
            machine,
            [q],
            [],
            [],
            [],
            for_verification=True,
            init_choice_logic=i,
        )
        init_cond = model.init[0]

        # Single-state strategies omit the redundant state variable.
        self.assertNotIn("strategy_state", init_cond)
        self.assertFalse(any(v.name == "strategy_state" for v in model.vars))
        self.assertIn("bin_keep", init_cond)
        self.assertIn("q", init_cond)
        self.assertNotIn("env_init_aux", init_cond)
        # The target state output constrains the first actual program step.
        self.assertIn("o", init_cond)
        self.assertNotIn("env_init_i", init_cond)

    def test_dual_moore_verification_init_keeps_target_output(self):
        i = Variable("env_init_i")
        o = Variable("o")
        machine = MooreMachine("counterstrategy", 0, [i], [o])
        machine.states = {"st_0", "st_1"}
        machine.out = {"st_0": BiOp(i, "&", UniOp("!", o)), "st_1": o}
        machine.transitions = {
            "st_0": [(i, "st_1")],
            "st_1": [(o, "st_1")],
        }

        model = strategy_to_nuxmv_model(
            machine, [], [], [], [], for_verification=True, init_choice_logic=i
        )
        init_cond = model.init[0]

        self.assertIn("strategy_state = st_1", init_cond)
        self.assertNotIn("strategy_state = st_0", init_cond)
        self.assertIn("(o)", init_cond)
        self.assertNotIn("!", init_cond)
        self.assertNotIn("env_init_i", init_cond)

    def test_dual_moore_verification_init_raises_if_qe_projection_is_false(self):
        i = Variable("i")
        o = Variable("o")
        machine = MooreMachine("counterstrategy", 0, [i], [o])
        machine.out = {"st_0": BiOp(i, "&", o)}
        machine.transitions = {"st_0": [(o, "st_0")]}

        with self.assertRaisesRegex(
            Exception,
            "Something wrong in LTL, no valid controller choice for initial state precicates",
        ):
            strategy_to_nuxmv_model(
                machine,
                [],
                [],
                [],
                [],
                for_verification=True,
                init_choice_logic=UniOp("!", o),
            )
