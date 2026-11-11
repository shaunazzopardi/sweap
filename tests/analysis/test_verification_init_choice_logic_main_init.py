from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.strategy_verification import (
    _init_choice_logic_for_main_init,
)
from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl
from config import Config
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class TestVerificationInitChoiceLogicMainInit(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_dual_moore_rewrites_next_for_main_init(self):
        self.conf.dual = True

        expr = _init_choice_logic_for_main_init(
            MooreMachine("counterstrategy", 0, [], []),
            SimpleNamespace(init_choice_logic=UniOp("next", Variable("env_init_0"))),
        )
        self.assertEqual(expr, "env_init_0")

    def test_base_mealy_does_not_add_init_choice_to_main_init(self):
        self.conf.dual = False

        expr = _init_choice_logic_for_main_init(
            MealyMachine("controller", 0, [], []),
            SimpleNamespace(init_choice_logic=UniOp("next", Variable("env_init_1"))),
        )
        self.assertIsNone(expr)

    def test_main_model_defines_and_uses_init_choice_logic_macro_in_init(self):
        self.conf.dual = False

        fake_program_model = StructuredNuXmvModel(
            name="prog",
            vars=[VarDecl("program_state", "{program_q_0}")],
            define=[],
            init=["program_state = program_q_0"],
            invar=["TRUE"],
            trans=["TRUE"],
        )
        fake_strategy_model = StructuredNuXmvModel(
            name="controller",
            vars=[VarDecl("strategy_state", "{st_0}")],
            define=[],
            init=["strategy_state = st_0"],
            invar=["TRUE"],
            trans=["TRUE"],
        )
        fake_program = SimpleNamespace(
            states={"s0"},
            states_binary_map={"s0": Variable("s0")},
            num_in_out=[],
            deterministic=True,
        )

        with patch(
            "analysis.compatibility_checking.compatibility_builder.program_to_nuxmv_model",
            return_value=fake_program_model,
        ):
            model_text = create_nuxmv_model_for_compatibility_checking(
                fake_program,
                fake_strategy_model,
                set(),
                set(),
                [],
                init_choice_logic_expr="env_init_0",
            )

        model_text = "\n".join(model_text.values())
        self.assertIn("init_choice_logic := env_init_0;", model_text)
        self.assertIn("\t& (init_choice_logic)", model_text)
