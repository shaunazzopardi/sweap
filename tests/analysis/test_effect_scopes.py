"""SMT scope reuse must preserve the abstract relation of a guarded update."""

import pytest

from analysis.abstraction.effects_abstraction.effects_abstraction import update_effects
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import (
    ChainPredicate,
)
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.sat_context import IncrementalSatContext
from config import Config
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import (
    conjunct,
    disjunct_formula_set,
    equivalent,
    true,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


@pytest.mark.parametrize("state_scopes, chain_scopes", [
    (False, False), (True, False), (False, True), (True, True),
])
def test_scopes_preserve_guarded_increment_effect(
    state_scopes, chain_scopes, monkeypatch
):
    conf = Config.getConfig()
    monkeypatch.setattr(conf, "opt_state_scopes", state_scopes)
    monkeypatch.setattr(conf, "opt_chain_scopes", chain_scopes)
    monkeypatch.setattr(conf, "debug", False)

    x = Variable("x")
    previous = x.prev_rep()
    symbols = {"x": INTEGER, "x_prev": INTEGER}
    zero, one = Value(0), Value(1)
    state_predicate = StatePredicate(BiOp(x, "=", zero), False)
    chain = ChainPredicate(x, None, False)
    chain.add_predicate([BiOp(x, "<=", zero), BiOp(x, "<=", one)])
    predicates = {state_predicate, chain}

    # x >= 0 guards x := x + 1. Predicates distinguish x<0, x=0,
    # x=1 and x>1, so exactly these abstract edges are possible:
    # zero -> one, one -> above-one, above-one -> above-one.
    guard_update = conjunct(
        BiOp(previous, ">=", zero),
        BiOp(x, "=", BiOp(previous, "+", one)),
    )
    with IncrementalSatContext(symbols, guard_update) as sat_ctx:
        effects = update_effects(
            effects=[(true(), [true()])],
            us=[Update(x, BiOp(x, "+", one))],
            gu=guard_update,
            curr_preds=(set(), set()),
            new_preds=predicates,
            partitions={0: {x}},
            v_to_partition={x: 0},
            v_to_preds={x: predicates},
            ignore_in_nows=set(),
            ignore_in_nexts=set(),
            symbol_table=symbols,
            sat_ctx=sat_ctx,
        )

    actual = disjunct_formula_set([
        conjunct(source.prev_rep(), disjunct_formula_set(targets))
        for source, targets in effects
    ])
    expected = disjunct_formula_set([
        conjunct(BiOp(previous, "=", zero), BiOp(x, "=", one)),
        conjunct(BiOp(previous, "=", one), BiOp(x, ">", one)),
        conjunct(BiOp(previous, ">", one), BiOp(x, ">", one)),
    ])
    assert equivalent(actual, expected, symbols)
