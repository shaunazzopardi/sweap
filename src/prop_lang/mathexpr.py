from typing import Any

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.value import Value
from prop_lang.variable import Variable


class MathExpr(Formula):
    def __init__(self, f: Formula):
        if isinstance(f, BiOp):
            if f.op in [
                "+",
                "-",
                "*",
                "/",
                "<",
                ">",
                "<=",
                ">=",
                "==",
                "=",
                "!=",
            ]:
                self.formula = f
            else:
                raise Exception("Unsupported operator: " + f.op)
        self.formula = f
        self.prev_representation = None

    def __str__(self):
        return str(self.formula)

    def __hash__(self):
        return self.formula.__hash__()

    def __eq__(self, other):
        if isinstance(other, MathExpr):
            return self.formula == other.formula
        else:
            return False

    def variablesin(self):
        return self.formula.variablesin()

    def ground(self, context):
        return MathExpr(self.formula.ground(context))

    def simplify(self):
        if isinstance(self.formula, BiOp) and self.formula.op in ["*"]:
            if isinstance(self.formula.left, Value) and self.formula.left.name == "1":
                return MathExpr(self.formula.right)
            elif (
                isinstance(self.formula.right, Value) and self.formula.right.name == "1"
            ):
                return MathExpr(self.formula.left)
        return self

    def ops_used(self):
        return []

    def replace_vars(self, context):
        return MathExpr(self.formula.replace_vars(context))

    def to_nuxmv(self):
        return MathExpr(self.formula.to_nuxmv())

    def to_strix(self):
        return self

    def to_smt(self, symbol_table: Any):
        return self.formula.to_smt(symbol_table)

    def replace_math_exprs(self, symbol_table, cnt=0):
        return Variable("math_" + str(cnt)), {("math_" + str(cnt)): self}

    def to_sympy(self):
        return self.formula.to_sympy()

    def replace_formulas(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return MathExpr(self.formula.replace_formulas(context))
        elif callable(context):
            ret = context(self)
            if ret is not None:
                return ret
            else:
                return MathExpr(self.formula.replace_formulas(context))
        else:
            return MathExpr(self.formula.replace_formulas(context))

    def prev_rep(self):
        if self.prev_representation is None:
            self.prev_representation = MathExpr(self.formula.prev_rep())
        return self.prev_representation

    def replace_formulas_multiple(self, context: dict):
        if self in context.keys():
            return context[self]
        else:
            return [
                MathExpr(f) for f in self.formula.replace_formulas_multiple(context)
            ]
