from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from analysis.compatibility_checking.compatibility_checking import (
    compatibility_checking,
)
from config import Config
from synthesis.machines.mealy_machine import MealyMachine


class TestSingleStateStrategyStateCeInjection(TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self._old_dual = self.conf.dual
        self.conf.dual = True

    def tearDown(self):
        self.conf.dual = self._old_dual

    def test_dual_single_state_injects_strategy_state_in_parsed_ce(self):
        strategy_machine = MealyMachine("controller", 0, [], [])
        fake_program = SimpleNamespace(
            states={"q0"},
            bin_state_vars=[],
            out_events=[],
            deterministic=True,
        )
        fake_predicate_abstraction = SimpleNamespace(
            get_program=lambda: fake_program,
            get_state_predicates=lambda: [],
            get_transition_predicates=lambda: [],
            v_to_chain_pred={},
        )
        fake_abstract_problem = SimpleNamespace(init_choice_logic=None)
        fake_strategy_nuxmv = SimpleNamespace(vars=[], name="controller")

        with patch(
            "analysis.compatibility_checking.compatibility_checking.strategy_to_nuxmv_model",
            return_value=fake_strategy_nuxmv,
        ), patch(
            "analysis.compatibility_checking.compatibility_checking.create_nuxmv_model_for_compatibility_checking",
            return_value={"main": "MODULE main"},
        ), patch(
            "analysis.compatibility_checking.compatibility_checking.there_is_mismatch_between_program_and_strategy",
            return_value=(False, True, "ce"),
        ), patch(
            "analysis.compatibility_checking.compatibility_checking.parse_nuxmv_ce_output_finite",
            return_value=(([], [], []), (None, {}, {})),
        ) as parse_call, patch(
            "analysis.compatibility_checking.compatibility_checking.concretize_transitions",
            return_value=([], {}),
        ):
            compatibility_checking(
                fake_program,
                fake_predicate_abstraction,
                strategy_machine,
                fake_abstract_problem,
                True,
            )

        self.assertEqual(parse_call.call_count, 1)
        self.assertEqual(
            parse_call.call_args.kwargs.get("injected_cs_constants"),
            {"strategy_state": "st_0"},
        )
