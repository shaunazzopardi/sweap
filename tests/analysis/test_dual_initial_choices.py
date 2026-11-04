import unittest
from types import SimpleNamespace
from unittest.mock import patch

from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.types import StructuredNuXmvModel
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.abstraction.effects_abstraction.to_ltl.one_trans_to_ltl import (
    abstract_ltl_problem,
)
from config import Config
from programs.transition import Transition
from prop_lang.types.types import BOOLEAN
from prop_lang.util import conjunct, neg, sat, true
from prop_lang.variable import Variable
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem


class TestDualInitialChoices(unittest.TestCase):
    def setUp(self):
        self.conf = Config.getConfig()
        self.addCleanup(setattr, self.conf, "dual", self.conf.dual)
        self.conf.dual = True

    def test_dual_builder_does_not_reapply_projected_init_choice(self):
        self.conf.dual = True
        program = SimpleNamespace(
            states={"q0"},
            states_binary_map={"q0": Variable("q0")},
            num_in_out=[],
            deterministic=True,
        )
        model = StructuredNuXmvModel(
            name="prog",
            vars=[],
            define=[],
            init=["TRUE"],
            invar=["TRUE"],
            trans=["TRUE"],
        )
        strategy = StructuredNuXmvModel(
            name="controller",
            vars=[],
            define=[],
            init=["TRUE"],
            invar=["TRUE"],
            trans=["TRUE"],
        )
        with patch(
            "analysis.compatibility_checking.compatibility_builder.program_to_nuxmv_model",
            return_value=model,
        ):
            text = create_nuxmv_model_for_compatibility_checking(
                program, strategy, set(), set(), [], init_choice_logic_expr="env_init_0"
            )
        self.assertIn("init_choice_logic := TRUE", text)
        self.assertNotIn("env_init_0", text)


def test_initial_choice_selects_one_predicate_valuation(monkeypatch):
    monkeypatch.setattr(Config.getConfig(), "dual", True)
    predicate = StatePredicate(Variable("ready"), False)
    state = Variable("q0")
    transition = Transition("q0", true(), [], [], "q0")
    program = SimpleNamespace(
        initial_state="q0",
        states_binary_map={"q0": state},
        bool_in_out=[],
        num_in_out=[],
        local_vars=[],
        symbol_table={},
        bin_state_vars=[state],
        out_events=[],
    )
    abstraction = SimpleNamespace(
        program=program,
        get_program=lambda: program,
        var_relabellings={predicate.pred: predicate.bool_var},
        input_preds=[],
        sat_input_models=[],
        sat_initial_input_models=None,
        init_state_abstraction=[[predicate.pred], [neg(predicate.pred)]],
        init_constants=[],
        state_predicates=[predicate],
        transition_predicates=[],
        v_to_chain_pred={},
        ranking_constraints={},
        structural_loop_constraints=[],
        loop_vars=[],
        gu_to_trans={0: [transition]},
        non_init_program_trans={transition},
        abstract_effect_ltl={0: true()},
        has_input_vars=lambda _: False,
    )
    problem = abstract_ltl_problem(LTLSynthesisProblem([], [], [], []), abstraction)
    selectors = [
        v
        for v in problem.ltl_synthesis_problem.env_props
        if str(v).startswith("env_init_")
    ]
    assert len(selectors) == 1
    selector = selectors[0]
    choice = problem.init_choice_logic
    assert choice in problem.get_guarantees()
    assert set(choice.variablesin()) == {selector, predicate.bool_var}
    symbols = {str(v): BOOLEAN for v in choice.variablesin()}
    allowed = []
    for value in (False, True):
        selected = conjunct(choice, selector if value else neg(selector))
        possibilities = [
            p
            for p in (False, True)
            if sat(
                conjunct(
                    selected, predicate.bool_var if p else neg(predicate.bool_var)
                ),
                symbols,
            )
        ]
        assert len(possibilities) == 1
        allowed.extend(possibilities)
    assert set(allowed) == {False, True}
