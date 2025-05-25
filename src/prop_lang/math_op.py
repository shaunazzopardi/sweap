from typing import Any

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.value import Value
from prop_lang.variable import Variable


class MathOp(Formula):
    def __init__(self, f: Formula):
        self.formula = f

    def __str__(self):
        return str(self.formula)

    def __hash__(self):
        return self.formula.__hash__()

    def __eq__(self, other):
        if isinstance(other, MathOp):
            return self.formula == other.formula
        else:
            return False

    def variablesin(self):
        return self.formula.variablesin()

    def ground(self, context):
        return MathOp(self.formula.ground(context))

    def simplify(self):
        if isinstance(self.formula, BiOp) and self.formula.op in ["*"]:
            if isinstance(self.formula.left, Value) and self.formula.left.name == "1":
                return MathOp(self.formula.right)
            elif (
                isinstance(self.formula.right, Value) and self.formula.right.name == "1"
            ):
                return MathOp(self.formula.left)
        return self

    def ops_used(self):
        return []

    def replace_vars(self, context):
        return MathOp(self.formula.replace_vars(context))

    def to_nuxmv(self):
        return MathOp(self.formula.to_nuxmv())

    def to_strix(self):
        return self

    def to_smt(self, symbol_table: Any):
        return self.formula.to_smt(symbol_table)

    def replace_math_exprs(self, symbol_table, cnt=0):
        return Variable("math_" + str(cnt)), {("math_" + str(cnt)): self}

    def to_sympy(self):
        raise Exception("Unsupported operator: " + self.op)

    def replace_formulas(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return MathOp(self.formula.replace_formulas(context))
        elif callable(context):
            if context(self) is not None:
                return context(self)
            else:
                return MathOp(self.formula.replace_formulas(context))
