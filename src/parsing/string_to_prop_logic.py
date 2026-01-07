from parsing import string_to_ltl
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr


def string_to_math_expression(text: str) -> MathExpr:
    formula = string_to_ltl.string_to_math_expression(text)
    return formula


def string_to_negated_atom(text: str) -> Formula:
    formula = string_to_ltl.string_to_negated_atom(text)
    return formula


def string_to_prop(text: str, hoa_flag=False) -> Formula:
    formula = string_to_ltl.string_to_prop(text, hoa_flag)
    return formula
