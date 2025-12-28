from pysmt.fnode import FNode

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import MathRels
from prop_lang.types.types import Type
from prop_lang.variable import Variable


class UpdateFormula(Formula):
    def __init__(self, f: Formula):
        if not any(
            v for v in f.variablesin() if isinstance(v, Variable) and v.is_next()
        ):
            raise Exception("UpdateFormula.formula must contain a next variable")
        self.formula = f

    def __str__(self):
        return str(self.formula)

    def __hash__(self):
        return str(self).__hash__()

    def __eq__(self, other):
        if isinstance(other, UpdateFormula):
            return self.formula == other.formula
        else:
            return False

    def variablesin(self):
        return self.formula.variablesin()

    def simplify(self):
        return UpdateFormula(self.formula.simplify())

    def ops_used(self):
        return []

    def replace_vars(self, context):
        return UpdateFormula(self.formula.replace_vars(context))

    def to_nuxmv(self):
        return self.formula.to_nuxmv()

    def to_strix(self):
        raise Exception("Update should not be used with TLSF")

    def to_smt(self, symbol_table: dict[str, Type]) -> tuple[FNode, FNode]:
        raise NotImplementedError("Update.to_smt is not implemented yet")

    def replace_math_exprs(self, symbol_table, cnt=0):
        raise Exception("Update should not be used with replace_math_exprs")

    def to_sympy(self):
        raise Exception("Update should not be used with sympy")

    def replace_formulas(self, context):
        return UpdateFormula(self.formula.replace_formulas(context))

    def prev_rep(self):
        return self.formula.prev_rep()

    def replace_formulas_multiple(self, context: dict):
        raise Exception("Update cannot be used with replace_formulas_multiple")
