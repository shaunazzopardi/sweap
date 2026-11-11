from unittest import TestCase

from analysis.compatibility_checking.strategy_to_nuxmv import (
    strategy_to_nuxmv_model,
)
from config import Config
from prop_lang.variable import Variable
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class TestSingleStateStrategyStateConstant(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual
        self.conf.dual = True

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_dual_single_state_mealy_omits_strategy_state_variable(self):
        i = Variable("i")
        o = Variable("o")
        machine = MealyMachine("controller", 0, [i], [o])
        machine.transitions = {"st_0": {"st_0": {(i, o)}}}

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [],
        )
        model_text = "\n".join(model.define + model.trans)

        self.assertFalse(any(v.name == "strategy_state" for v in model.vars))
        self.assertNotIn("strategy_state = st_0", model_text)
        self.assertNotIn("strategy_state =", model_text)
        self.assertNotIn("next(strategy_state)", model_text)

    def test_dual_single_state_moore_omits_strategy_state_variable(self):
        i = Variable("i")
        o = Variable("o")
        machine = MooreMachine("counterstrategy", 0, [i], [o])
        machine.out = {"st_0": o}
        machine.transitions = {"st_0": [(o, "st_0")]}

        model = strategy_to_nuxmv_model(
            machine,
            [],
            [],
            [],
            [],
            for_verification=True,
        )
        model_text = "\n".join(model.define + model.trans)

        self.assertFalse(any(v.name == "strategy_state" for v in model.vars))
        self.assertNotIn("strategy_state = st_0", model_text)
        self.assertNotIn("strategy_state =", model_text)
        self.assertNotIn("next(strategy_state)", model_text)
