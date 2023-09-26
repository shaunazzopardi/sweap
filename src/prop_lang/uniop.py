import sympy.core.logic
from pysmt.fnode import FNode
from pysmt.shortcuts import Not, Minus, Int

from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula
from prop_lang.value import Value
from prop_lang.variable import Variable

class UniOp(Formula):
    def __init__(self, op: str, right: Formula):
        if not isinstance(right, Formula):
            print()
        self.op = op
        self.right = right

    def __str__(self):
        if self.op == "next" and (
                isinstance(self.right, UniOp) or isinstance(self.right, Value) or isinstance(self.right, Variable)):
            return self.op + "(" + str(self.right) + ")"
        if self.op in ["G,F,X"]:
            return self.op + "(" + str(self.right) + ")"
        if self.op != "!" and self.op != "-":
            return self.op + " " + str(self.right)
        else:
            return self.op + str(self.right)

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, UniOp):
            return self.op == other.op and self.right == other.right
        else:
            return NotImplemented

    def __hash__(self):
        return hash((self.op, self.right))

    def variablesin(self) -> [Variable]:
        return self.right.variablesin()

    def ground(self, context: [TypedValuation]):
        return UniOp(self.op, self.right.ground(context))

    def simplify(self):
        right = self.right.simplify()
        if self.op in ["!"]:
            if isinstance(right, UniOp) and right.op == "!":
                return right.right
            elif isinstance(right, Value) and right.is_true():
                return Value("False")
            elif isinstance(right, Value) and right.is_false():
                return Value("True")
        return UniOp(self.op, right)

    def ops_used(self):
        return [self.op] + self.right.ops_used()

    def replace_vars(self, context):
        return UniOp(self.op, self.right.replace_vars(context))

    def to_nuxmv(self):
        return UniOp(self.op, self.right.to_nuxmv())

    def to_strix(self):
        return UniOp(self.op, self.right.to_strix())

    def to_smt(self, symbol_table) -> (FNode, FNode):
        expr, invar = self.right.to_smt(symbol_table)
        if self.op == "!":
            return Not(expr), invar
        elif self.op == "-":
            return Minus(Int(0), expr), invar
        else:
            raise NotImplementedError(f"{self.op} unsupported")

    def replace_math_exprs(self, symbol_table, cnt=0):
        new_right, dic = self.right.replace_math_exprs(symbol_table, cnt)
        if len(dic) == 0:
            if self.op == "-" or self.op == "+":
                new_right, dic = Variable("math_" + str(cnt)), {Variable("math_" + str(cnt)): self}
        return UniOp(self.op, new_right), dic

    def to_sympy(self):
        if self.op == "!":
            return sympy.Not(self.right.to_sympy())

    def replace_formulas(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return UniOp(self.op, self.right.replace_formulas(context))
        elif callable(context):
            if context(self) is not None:
                return context(self)
            else:
                return UniOp(self.op, self.right.replace_formulas(context))
