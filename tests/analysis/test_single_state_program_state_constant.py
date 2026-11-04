from types import SimpleNamespace
from unittest import TestCase

from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.program_to_nuxmv import (
    program_to_nuxmv_model,
)
from analysis.compatibility_checking.types import StructuredNuXmvModel
from config import Config
from prop_lang.util import true
from prop_lang.variable import Variable


class _DummyProgram:
    def __init__(self):
        self.name = "p"
        self.states = {"s0"}
        self.initial_state = "s0"
        self.local_vars_str = set()
        self.local_vars = []
        self.num_in_out = []
        self.env_events = []
        self.out_events = []
        self.bool_in_out = []
        self.symbol_table = {}
        self.init_var_values = {}
        self.deterministic = True
        self.states_binary_map = {"s0": Variable("s0")}
        self.transitions = [
            SimpleNamespace(
                src="s0",
                tgt="s0",
                condition=true(),
                pred_upgrades=[],
                action=[],
                output=[],
            )
        ]

    @staticmethod
    def complete_action_set(action):
        return action


class TestSingleStateProgramStateConstant(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual
        self.conf.dual = False

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_single_state_program_model_omits_program_state_variable(self):
        program = _DummyProgram()
        model = program_to_nuxmv_model(program)
        model_text = "\n".join(model.define + model.init + model.trans)

        self.assertFalse(any(v.name == "program_state" for v in model.vars))
        self.assertNotIn("program_state =", model_text)
        self.assertNotIn("next(program_state)", model_text)
        self.assertIn("s0 := TRUE", model_text)

    def test_single_state_main_aliases_do_not_reference_program_state(self):
        program = _DummyProgram()
        strategy_model = StructuredNuXmvModel(
            name="controller",
            vars=[],
            define=[],
            init=["TRUE"],
            invar=["TRUE"],
            trans=["TRUE"],
        )

        model_text = create_nuxmv_model_for_compatibility_checking(
            program,
            strategy_model,
            set(),
            set(),
            [],
        )

        self.assertIn("s0 := TRUE;", model_text)
        self.assertNotIn("program_state =", model_text)
        self.assertNotIn("next(program_state)", model_text)
