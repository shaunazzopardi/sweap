"""Semantic regressions for formula substitution, projection and normal forms."""

import pytest

from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.util import (
    cnf,
    conjunct,
    disjunct,
    dnf,
    equivalent,
    is_dnf,
    keep_only_vars,
    normalise_mathexpr,
    partially_evaluate,
    prime_action,
    project_out_vars,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


@pytest.mark.parametrize("value", [False, True])
def test_partial_evaluation_substitutes_both_truth_values(value):
    p, q = Variable("p"), Variable("q")
    result = partially_evaluate(
        conjunct(p, q),
        [p] if value else [],
        [] if value else [p],
        {"p": BOOLEAN, "q": BOOLEAN},
    )
    assert result == (q if value else Value("FALSE"))


@pytest.mark.parametrize("project", [keep_only_vars, project_out_vars])
def test_projection_removes_only_the_requested_variable(project):
    p, q, r = map(Variable, ("p", "q", "r"))
    symbols = {"p": BOOLEAN, "q": BOOLEAN, "r": BOOLEAN}
    formula = conjunct(conjunct(p, q), r)
    selected = [p, q] if project is keep_only_vars else [r]
    result = project(formula, selected)
    assert equivalent(result, conjunct(p, q), symbols)
    assert r not in result.variablesin()


def test_prime_action_shifts_only_assignment_target():
    x, y = Variable("x"), Variable("y")
    action = BiOp(x, "=", BiOp(y, "+", Value(1)))
    assert prime_action([action]) == BiOp(
        Variable("x_next"), "=", BiOp(y, "+", Value(1))
    )


@pytest.mark.parametrize("normal_form", ["cnf", "dnf"])
def test_normal_form_distributes_and_preserves_truth_table(normal_form):
    p, q, r = map(Variable, ("p", "q", "r"))
    symbols = {"p": BOOLEAN, "q": BOOLEAN, "r": BOOLEAN}
    if normal_form == "dnf":
        formula = conjunct(disjunct(p, q), r)
        result = dnf(formula)
        assert is_dnf(result)
    else:
        formula = disjunct(conjunct(p, q), r)
        result = cnf(formula, symbols)
        clauses = result.sub_formulas_up_to_associativity()
        assert result.op == "&"
        assert all(isinstance(c, BiOp) and c.op == "|" for c in clauses)
    assert equivalent(result, formula, symbols)


@pytest.mark.parametrize("op", [">", "<", "=", "!=", ">=", "<="])
def test_numeric_normalisation_preserves_comparison(op):
    x, y = Variable("x"), Variable("y")
    formula = BiOp(BiOp(x, "+", Value(1)), op, BiOp(y, "-", Value(2)))
    result = normalise_mathexpr(formula)
    assert equivalent(formula, result, {"x": INTEGER, "y": INTEGER})

    def comparison_operators(node):
        if isinstance(node, MathExpr):
            return comparison_operators(node.formula)
        if isinstance(node, UniOp):
            return comparison_operators(node.right)
        if isinstance(node, BiOp):
            own = [node.op] if node.op in {">", "<", "=", "!=", ">=", "<="} else []
            return (
                own + comparison_operators(node.left) + comparison_operators(node.right)
            )
        return []

    assert set(comparison_operators(result)) == {"<="}
