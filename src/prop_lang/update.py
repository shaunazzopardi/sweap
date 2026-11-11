from pysmt.fnode import FNode

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import MathRels
from prop_lang.types.types import Type
from prop_lang.variable import Variable


class Update(Formula):
    def __init__(self, v: Variable, f: Formula):
        self.left = v
        self.right = f
        self.prev_representation = None

    def __str__(self):
        return str(self.left) + " := " + str(self.right)

    def __hash__(self):
        return str(self).__hash__()

    def __eq__(self, other):
        if isinstance(other, Update):
            return self.left == other.left and self.right == other.right
        else:
            return False

    def variablesin(self):
        return [self.left] + self.right.variablesin()

    def simplify(self):
        return self

    def ops_used(self):
        return []

    def replace_vars(self, context):
        return Update(self.left.replace_vars(context), self.right.replace_vars(context))

    def to_nuxmv(self):
        return "next(" + self.left.to_nuxmv() + ") = " + self.right.to_nuxmv()

    def to_strix(self):
        raise Exception("Update should not be used with TLSF")

    def to_smt(self, symbol_table: dict[str, Type]) -> tuple[FNode, FNode]:
        raise NotImplementedError("Update.to_smt is not implemented yet")

    def replace_math_exprs(self, symbol_table, cnt=0):
        raise Exception("Update should not be used with replace_math_exprs")

    def to_sympy(self):
        raise Exception("Update should not be used with sympy")

    def replace_formulas(self, context):
        if isinstance(context, dict) and self in context.keys():
            return context[self]
        elif callable(context) and (ret := context(self)):
            return ret
        else:
            return Update(
                self.left.replace_formulas(context),
                self.right.replace_formulas(context),
            )

    def prev_rep(self):
        if not self.prev_representation:
            self.prev_representation = BiOp(
                self.left, MathRels.EQ, self.right.prev_rep()
            )
        return self.prev_representation

    def replace_formulas_multiple(self, context: dict):
        raise Exception("Update cannot be used with replace_formulas_multiple")
