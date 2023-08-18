from pysmt.fnode import FNode
from pysmt.shortcuts import And, Or, Implies
from pysmt.shortcuts import (
    Plus, Minus, Times, Div, BVSRem, EqualsOrIff, LE, LT, GT, GE, NotEquals
)

from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class BiOp(Formula):
    def __init__(self, left: Formula, op: str, right: Formula):
        if left == None:
            raise Exception("BiOp: left is None")
        if right == None:
            raise Exception("BiOp: right is None")
        assert(isinstance(left, Formula), "left is not a formula")
        self.left = left
        self.op = op.strip()
        assert(isinstance(right, Formula), "right is not a formula")
        self.right = right

    def __str__(self):
        if len(self.sub_formulas_up_to_associativity()) == 1:
            return "(" + str(self.left) + " " + self.op + " " + str(self.right) + ")"
        else:
            return "(" + (" " + self.op + " ").join([str(c) for c in self.sub_formulas_up_to_associativity()]) + ")"

    def sub_formulas_up_to_associativity(self):
        if self.op == "&&" or self.op == "&" or self.op == "||" or self.op == "|":
            sub_formulas = []
            if not isinstance(self.left, BiOp) or self.left.op != self.op:
                sub_formulas += [self.left]
            else:
                sub_formulas += self.left.sub_formulas_up_to_associativity()
            if not isinstance(self.right, BiOp) or self.right.op != self.op:
                sub_formulas += [self.right]
            else:
                sub_formulas += self.right.sub_formulas_up_to_associativity()
        else:
            sub_formulas = [self]
        return sub_formulas

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, BiOp):
            return self.op == other.op and self.right == other.right and self.left == other.left
        return NotImplemented

    def __hash__(self):
        return hash((self.left, self.op, self.right))

    # returns list of variables that appear in formula
    # ordered as they appear in the formula
    # without already appearing variables
    def variablesin(self) -> [Variable]:
        vars = self.left.variablesin() + self.right.variablesin()
        vars_unique = [v for (i, v) in enumerate(vars) if v not in vars[:i]]
        return vars_unique

    def ground(self, context: [TypedValuation]):
        return BiOp(self.left.ground(context), self.op, self.right.ground(context))

    def simplify(self):
        left = self.left.simplify()
        right = self.right.simplify()
        if self.op in ["&", "&&"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return left
            elif isinstance(right, Value) and right.is_true():
                return left
            elif isinstance(right, Value) and right.is_false():
                return right
        elif self.op in ["|", "||"]:
            if isinstance(left, Value) and left.is_true():
                return left
            elif isinstance(left, Value) and left.is_false():
                return right
            elif isinstance(right, Value) and right.is_true():
                return right
            elif isinstance(right, Value) and right.is_false():
                return left
        elif self.op in ["->", "=>"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return Value("True")
            elif isinstance(right, Value) and right.is_true():
                return Value("True")
            elif isinstance(right, Value) and right.is_false():
                return UniOp("!", left)
        elif self.op in ["<->", "<=>"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return UniOp("!", right).simplify()
            elif isinstance(right, Value) and right.is_true():
                return left
            elif right == left:
                return Value("True")
            elif isinstance(right, Value) and right.is_false():
                return UniOp("!", left).simplify()
        elif self.op in ["=="]:
            if right == left:
                return Value("True")
        return self

    def ops_used(self):
        return [self.op] + self.left.ops_used() + self.right.ops_used()

    def replace(self, context):
        return BiOp(self.left.replace(context), self.op, self.right.replace(context))

    def to_nuxmv(self):
        if self.op == "%":
            return UniOp("toint", BiOp(UniOp("unsigned word[8]", self.left.to_nuxmv()), "mod",
                                       UniOp("unsigned word[8]", self.right.to_nuxmv())))
        elif self.op == "==":
            return BiOp(self.left.to_nuxmv(), '==', self.right.to_nuxmv())
        elif self.op == "=>":
            return BiOp(self.left.to_nuxmv(), '->', self.right.to_nuxmv())
        elif self.op == "<=>":
            return BiOp(self.left.to_nuxmv(), '<->', self.right.to_nuxmv())
        elif self.op == "&&":
            return BiOp(self.left.to_nuxmv(), '&', self.right.to_nuxmv())
        elif self.op == "||":
            return BiOp(self.left.to_nuxmv(), '|', self.right.to_nuxmv())
        elif self.op == "W":
            return BiOp(BiOp(self.left, "U", self.right), "|", UniOp("G", self.left)).to_nuxmv()
        elif self.op == "R":
            return BiOp(self.right, "W", BiOp(self.right, "&", self.left)).to_nuxmv()
        elif self.op == "M":
            return BiOp(self.right, "U", BiOp(self.right, "&", self.left)).to_nuxmv()
        else:
            return BiOp(self.left.to_nuxmv(), self.op, self.right.to_nuxmv())

    def to_smt(self, symbol_table) -> (FNode, FNode):
        ops = {
            "&": And,
            "&&": And,
            "|": Or,
            "||": Or,
            "->": Implies,
            "=>": Implies,
            "==": EqualsOrIff,
            "=": EqualsOrIff,
            "!=": NotEquals,
            "<->": EqualsOrIff,
            ">": GT,
            ">=": GE,
            "<": LT,
            "<=": LE,
            "+": Plus,
            "-": Minus,
            "*": Times,
            "/": Div,
            "%": BVSRem
        }
        left_expr, left_invar = self.left.to_smt(symbol_table)
        right_expr, right_invar = self.right.to_smt(symbol_table)

        try:
            op = ops[self.op]
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
        else:
            return op(left_expr, right_expr), And(left_invar, right_invar)

    def replace_math_exprs(self, symbol_table, cnt=0):
        new_left, dic_left = self.left.replace_math_exprs(symbol_table, cnt)
        new_right, dic_right = self.right.replace_math_exprs(symbol_table, cnt + len(dic_left))
        if len(dic_left) == 0 and len(dic_right) == 0:
            if self.op == "=" or self.op == "==" or self.op == "!=" or self.op == "<=" or self.op == ">=" or self.op == "<" or self.op == ">":
                return Variable("math_" + str(cnt)), {Variable("math_" + str(cnt)): self}
        return BiOp(new_left, self.op, new_right), dic_left | dic_right