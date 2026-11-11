from unittest import TestCase
from types import SimpleNamespace

from analysis.compatibility_checking.strategy_to_nuxmv import (
    strategy_to_nuxmv_model,
)
from config import Config
from prop_lang.biop import BiOp
from prop_lang.variable import Variable
from synthesis.machines.moore_machine import MooreMachine


class TestDualMooreGuardNexting(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual
        self.conf.dual = True

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_dual_moore_guards_next_controller_pred_and_bin(self):
        pred_x = Variable("pred__x")
        bin_x = Variable("bin_x")
        sat_cp = Variable("sat_con_cp_0_0")
        q = Variable("q")
        o = Variable("o")
        i = Variable("i")

        machine = MooreMachine(
            "counterstrategy", 0, [i], [pred_x, bin_x, sat_cp, q, o]
        )
        machine.out = {"st_0": o}
        machine.transitions = {
            "st_0": [
                (
                    BiOp(BiOp(BiOp(pred_x, "&", bin_x), "&", sat_cp), "&", q),
                    "st_0",
                )
            ]
        }
        trans_pred = SimpleNamespace(bool_rep={Variable("dummy"): sat_cp})

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [trans_pred],
            for_verification=True,
        )
        guard_0 = next(
            d for d in model.define if d.startswith("counterstrategy_guard_0 :=")
        )

        self.assertIn("next(pred__x)", guard_0)
        self.assertIn("next(bin_x)", guard_0)
        self.assertIn("next(sat_con_cp_0_0)", guard_0)
        self.assertIn(" q", guard_0)
        self.assertNotIn("next(q)", guard_0)
