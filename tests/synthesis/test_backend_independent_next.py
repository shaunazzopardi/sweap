from types import SimpleNamespace

import pytest

import config
from analysis.abstraction.effects_abstraction.effects_abstraction import effects_to_ltl
from analysis.abstraction.effects_abstraction.to_ltl.one_trans_to_ltl import (
    massage_models_for_dual,
)
from prop_lang.util import X, conjunct, disjunct, neg
from prop_lang.variable import Variable
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem


@pytest.mark.parametrize('backend', config.synthesis_backends)
def test_tlsf_preserves_compound_next(backend, monkeypatch):
    monkeypatch.setattr(config.Config.getConfig(), 'backend', backend)
    a, b, o = map(Variable, ('a', 'b', 'o'))
    problem = LTLSynthesisProblem(
        [a, b], [o], [neg(X(disjunct(neg(a), neg(b))))],
        [X(conjunct(o, X(o)))],
    )
    assert '!X((!a || !b))' in problem.tlsf
    assert 'X((o && X(o)))' in problem.tlsf


@pytest.mark.parametrize('dual', [False, True])
def test_effects_use_the_same_formula_for_every_backend(dual):
    a, b, c = map(Variable, ('a', 'b', 'c'))
    compound = disjunct(a, b)
    formulas = [
        effects_to_ltl(
            {(): [(c, [compound])]}, [c], [],
            SimpleNamespace(backend=backend, dual=dual), {}, {}, {c: X(compound)},
        )
        for backend in config.synthesis_backends
    ]
    assert all(formula == formulas[0] for formula in formulas[1:])
    assert 'X((a | b))' in str(formulas[0])


def test_dual_input_models_preserve_compound_next(monkeypatch):
    a, b, predicate = map(Variable, ('a', 'b', 'predicate'))
    abstraction = SimpleNamespace(
        var_relabellings={predicate: disjunct(a, b)},
        sat_input_models=[predicate],
    )
    formulas = []
    for backend in config.synthesis_backends:
        monkeypatch.setattr(config.Config.getConfig(), 'backend', backend)
        formulas.append(massage_models_for_dual([predicate], abstraction))
    assert all(formula == formulas[0] for formula in formulas[1:])
    assert 'X((a | b))' in str(formulas[0][0])
