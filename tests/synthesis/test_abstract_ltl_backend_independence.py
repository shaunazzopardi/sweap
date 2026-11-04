from types import SimpleNamespace

import pytest

import config
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.abstraction.effects_abstraction.to_ltl.one_trans_to_ltl import (
    abstract_ltl_problem,
)
from programs.transition import Transition
from prop_lang.types.types import BOOLEAN
from prop_lang.util import F, G, X, conjunct, disjunct, implies, neg, true
from prop_lang.variable import Variable
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem


@pytest.fixture
def three_location_abstraction():
    """A prepared effects abstraction with both kinds of fairness refinement."""
    q0, q1, q2 = map(Variable, ('q0', 'q1', 'q2'))
    bit0, bit1 = map(Variable, ('bin_st_0', 'bin_st_1'))
    ready, done, in_loop, grant = map(
        Variable, ('ready', 'done', 'in_loop', 'grant')
    )
    state_predicates = [StatePredicate(p, False) for p in (ready, done)]
    relabellings = {p.pred: p.bool_var for p in state_predicates}
    state_map = {
        q0: conjunct(neg(bit0), neg(bit1)),
        q1: conjunct(neg(bit0), bit1),
        q2: conjunct(bit0, neg(bit1)),
    }
    transitions = [
        Transition(q0, true(), [], [], q1),
        Transition(q1, true(), [], [], q2),
        Transition(q2, true(), [], [], q0),
    ]
    program = SimpleNamespace(
        initial_state=q0,
        states_binary_map=state_map,
        bin_state_vars=[bit0, bit1],
        bool_in_out=[grant],
        num_in_out=[],
        out_events=[],
        local_vars=[ready, done],
        symbol_table={'ready': BOOLEAN, 'done': BOOLEAN},
    )
    # This is the consequent of a recurrence constraint keyed by its trigger.
    ranking = G(F(X(disjunct(ready, done))))
    structural = G(implies(in_loop, X(disjunct(q1, q2))))
    abstraction = SimpleNamespace(
        program=program,
        get_program=lambda: program,
        var_relabellings=relabellings,
        input_preds=[],
        sat_input_models=[],
        sat_initial_input_models=None,
        state_predicates=state_predicates,
        transition_predicates=[],
        v_to_chain_pred={},
        ranking_constraints={ready: [ranking]},
        structural_loop_constraints=[structural],
        loop_vars=[in_loop],
        init_state_abstraction=[[ready, neg(done)]],
        init_constants=[],
        gu_to_trans={index: [t] for index, t in enumerate(transitions)},
        non_init_program_trans=transitions,
        abstract_effect_ltl={
            index: X(disjunct(relabellings[ready], relabellings[done]))
            for index in range(len(transitions))
        },
    )
    original = LTLSynthesisProblem([], [grant], [], [G(F(done))])
    replacements = state_map | relabellings
    return (
        abstraction,
        original,
        implies(G(F(ready)), ranking).replace_formulas(replacements),
        structural.replace_formulas(replacements),
        X(state_map[q1]),
    )


@pytest.mark.parametrize('dual', [False, True])
def test_complete_abstraction_is_backend_independent(
    three_location_abstraction, dual, monkeypatch
):
    abstraction, original, ranking, structural, next_target = (
        three_location_abstraction
    )
    conf = config.Config.getConfig()
    monkeypatch.setattr(conf, 'dual', dual)
    problems = []
    for backend in config.synthesis_backends:
        monkeypatch.setattr(conf, 'backend', backend)
        problem = abstract_ltl_problem(original, abstraction)
        constraints = problem.get_guarantees() if dual else problem.get_assumptions()
        assert ranking in constraints
        assert structural in constraints
        assert any(str(next_target) in str(f) for f in constraints)
        problems.append(problem)

    for problem in problems[1:]:
        assert problem.get_assumptions() == problems[0].get_assumptions()
        assert problem.get_guarantees() == problems[0].get_guarantees()
        assert problem.tlsf == problems[0].tlsf
