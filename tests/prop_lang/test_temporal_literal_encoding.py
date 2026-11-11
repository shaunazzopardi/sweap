from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    X,
    formula_with_next_to_without,
    iff,
    is_tautology,
    neg,
    false,
    simplify_formula_without_math,
)
from prop_lang.variable import Variable


def test_next_negation_has_the_same_boolean_encoding():
    p = Variable("p")
    left = formula_with_next_to_without(X(neg(p)))
    right = formula_with_next_to_without(neg(X(p)))
    assert is_tautology(iff(left, right), {"p_next": BOOLEAN})
    assert is_tautology(iff(left, neg(Variable("p_next"))), {"p_next": BOOLEAN})


def test_formula_simplification_removes_not_false():
    a = Variable("a")
    assert simplify_formula_without_math(BiOp(a, "&", UniOp("!", false()))) == a
