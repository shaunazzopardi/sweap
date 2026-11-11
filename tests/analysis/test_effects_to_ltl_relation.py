"""Effects rendering preserves an independently specified transition relation."""

import itertools
import random
from types import SimpleNamespace

import pytest
from analysis.abstraction.effects_abstraction.effects_abstraction import effects_to_ltl
from prop_lang.types.types import BOOLEAN
from prop_lang.util import X, conjunct, formula_with_next_to_without, neg, sat
from prop_lang.variable import Variable


@pytest.mark.parametrize("seed", [13, 23, 37, 97])
@pytest.mark.parametrize("dual", [False, True])
def test_effect_formula_matches_explicit_transition_relation(seed, dual):
    p, q = Variable("p"), Variable("q")
    states = list(itertools.product((False, True), repeat=2))
    edges = random.Random(seed).sample(list(itertools.product(states, repeat=2)), 7)

    def cube(state):
        return conjunct(p if state[0] else neg(p), q if state[1] else neg(q))

    entries = [(cube(source), [cube(target)]) for source, target in edges]
    state_p, input_q = Variable("state_p"), Variable("input_q")
    relabelling = {p: state_p, q: input_q}
    dual_relabelling = {p: state_p, q: X(input_q)}
    formula = effects_to_ltl(
        {(): entries}, [], [], SimpleNamespace(dual=dual), {},
        relabelling, dual_relabelling,
    )
    formula = formula_with_next_to_without(formula)
    variables = [Variable(name) for name in ("state_p", "input_q", "state_p_next", "input_q_next")]
    symbols = {str(v): BOOLEAN for v in variables}
    for source, target in itertools.product(states, repeat=2):
        valuation = source + target
        assigned = formula
        for var, value in zip(variables, valuation):
            assigned = conjunct(assigned, var if value else neg(var))
        # Dual source conditions observe the input at the next time step,
        # while the state predicate still refers to the current state.
        observed_source = (source[0], target[1]) if dual else source
        assert sat(assigned, symbols) == ((observed_source, target) in edges)
