"""Temporary solver constraints must not leak into their parent context."""

import pytest

from analysis.abstraction.effects_abstraction.scoped_effects_update import (
    _push_sat_formula,
)
from analysis.sat_context import IncrementalSatContext, NonIncrementalSatContext
from prop_lang.types.types import BOOLEAN
from prop_lang.util import false, neg, true
from prop_lang.variable import Variable


@pytest.fixture(params=[False, True], ids=["empty", "with-base"])
def context(request):
    p = Variable("p")
    base = p if request.param else None
    with IncrementalSatContext({"p": BOOLEAN, "q": BOOLEAN}, base) as ctx:
        yield ctx, base


def test_queries_do_not_accumulate_constraints(context):
    ctx, base = context
    p = Variable("p")
    with NonIncrementalSatContext(ctx.symbol_table, base) as fresh:
        for formula in [p, neg(p), false(), true(), neg(p), p]:
            assert ctx.is_sat(formula) == fresh.is_sat(formula)


def test_nested_scopes_restore_parent_and_base(context):
    ctx, base = context
    p, q = Variable("p"), Variable("q")
    with _push_sat_formula(ctx, true()):
        assert ctx.is_sat(neg(q))
        with _push_sat_formula(ctx, q):
            assert ctx.is_sat(q)
            assert not ctx.is_sat(neg(q))
            with _push_sat_formula(ctx, neg(q)):
                assert not ctx.is_sat(true())
            # Popping the contradictory inner scope preserves the outer q.
            assert ctx.is_sat(q)
            assert not ctx.is_sat(neg(q))
        # The sibling scope must not inherit q from the preceding one.
        with _push_sat_formula(ctx, neg(q)):
            assert not ctx.is_sat(q)
            assert ctx.is_sat(neg(q))
    assert ctx.is_sat(q)
    assert ctx.is_sat(neg(q))
    assert ctx.is_sat(neg(p)) == (base is None)


@pytest.mark.parametrize("operation", ["query", "scope"])
@pytest.mark.parametrize("failure", ["conversion", "assertion", "solve"])
def test_failed_operations_restore_existing_scope(context, operation, failure, monkeypatch):
    ctx, base = context
    p, q = Variable("p"), Variable("q")

    def fail(*args, **kwargs):
        raise RuntimeError("injected failure")

    add_assertion = ctx._solver.add_assertion

    def add_then_fail(formula):
        # Even a failure after an assertion is added must roll it back.
        add_assertion(formula)
        fail()

    with _push_sat_formula(ctx, q):
        with pytest.raises(RuntimeError, match="injected failure"):
            with monkeypatch.context() as patch:
                if failure == "conversion":
                    patch.setattr(ctx, "_to_smt", fail)
                elif failure == "assertion":
                    patch.setattr(ctx._solver, "add_assertion", add_then_fail)
                else:
                    patch.setattr(ctx._solver, "solve", fail)
                if operation == "query":
                    ctx.is_sat(neg(q))
                else:
                    with _push_sat_formula(ctx, neg(q)):
                        ctx._solver.solve()
        assert ctx.is_sat(q)
        assert not ctx.is_sat(neg(q))
    assert ctx.is_sat(neg(q))
    assert ctx.is_sat(neg(p)) == (base is None)


def test_scope_body_exception_restores_context(context):
    ctx, _ = context
    q = Variable("q")
    with pytest.raises(ValueError, match="body failed"):
        with _push_sat_formula(ctx, q):
            raise ValueError("body failed")
    assert ctx.is_sat(neg(q))


def test_unsatisfiable_base_survives_scope_removal():
    with IncrementalSatContext({}, false()) as ctx:
        with _push_sat_formula(ctx, true()):
            assert not ctx.is_sat(true())
        assert not ctx.is_sat(true())
