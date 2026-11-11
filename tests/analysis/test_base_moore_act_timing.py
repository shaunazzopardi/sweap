from unittest import TestCase

from analysis.compatibility_checking.strategy_to_nuxmv import (
    strategy_to_nuxmv_model,
)
from config import Config
from prop_lang.biop import BiOp
from prop_lang.variable import Variable
from synthesis.machines.moore_machine import MooreMachine


class TestBaseMooreActTiming(TestCase):
    def setUp(self):
        conf = Config.getConfig()
        self._old_dual = conf.dual
        conf.dual = False

    def tearDown(self):
        conf = Config.getConfig()
        conf.dual = self._old_dual

    def test_base_flow_act_nexts_outputs_and_init_includes_init_output(self):
        entry = Variable("entry")
        pred = Variable("pred__p")
        bin_var = Variable("bin_x")
        out_flag = Variable("l2r")

        machine = MooreMachine(
            "controller",
            0,
            [entry],
            [pred, bin_var, out_flag],
        )
        machine.states = {"st_0", "st_1"}
        machine.transitions = {
            "st_0": [(out_flag, "st_1")],
            "st_1": [(out_flag, "st_1")],
        }
        machine.out = {
            "st_0": BiOp(BiOp(pred, "&", bin_var), "&", BiOp(out_flag, "&", entry)),
            "st_1": BiOp(pred, "&", out_flag),
        }

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [],
            for_verification=True,
        )

        init_cond = model.init[0]
        self.assertIn("strategy_state = st_0", init_cond)
        self.assertIn("l2r", init_cond)
        self.assertIn("pred__p", init_cond)
        self.assertIn("bin_x", init_cond)
        self.assertIn("entry", init_cond)
        model_text = "\n".join(model.define)
        self.assertIn("next(strategy_state)", model_text)
        self.assertIn("next(pred__p)", model_text)
        self.assertIn("next(l2r)", model_text)
