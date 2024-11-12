import sympy
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
        self.vars = None

        self.prev_representation = None

    def __str__(self):
        if len(self.sub_formulas_up_to_associativity()) == 1:
            return "(" + str(self.left) + " " + self.op + " " + str(self.right) + ")"
        else:
            return "(" + (" " + self.op + " ").join([str(c) for c in self.sub_formulas_up_to_associativity()]) + ")"

    def sub_formulas_up_to_associativity(self):
        if self.op == "&&" or self.op == "&":
            is_same_as_op = lambda x: x[0] == "&"
        elif self.op == "||" or self.op == "|":
            is_same_as_op = lambda x: x[0] == "|"
        else:
            return [self]

        sub_formulas = []
        if not isinstance(self.left, BiOp) or not is_same_as_op(self.left.op):
            sub_formulas += [self.left]
        else:
            sub_formulas += self.left.sub_formulas_up_to_associativity()
        if not isinstance(self.right, BiOp) or not is_same_as_op(self.right.op):
            sub_formulas += [self.right]
        else:
            sub_formulas += self.right.sub_formulas_up_to_associativity()
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
        if self.vars is not None:
            return self.vars
        vars = self.left.variablesin() + self.right.variablesin()
        vars_unique = [v for (i, v) in enumerate(vars) if v not in vars[:i]]
        self.vars = vars_unique
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
        return BiOp(left, self.op, right)

    def ops_used(self):
        return [self.op] + self.left.ops_used() + self.right.ops_used()

    def replace_vars(self, context):
        return BiOp(self.left.replace_vars(context), self.op, self.right.replace_vars(context))

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

    def to_strix(self):
        if self.op == "==":
            return BiOp(self.left.to_strix(), '==', self.right.to_strix())
        elif self.op == "=>":
            return BiOp(self.left.to_strix(), '->', self.right.to_strix())
        elif self.op == "<=>":
            return BiOp(self.left.to_strix(), '<->', self.right.to_strix())
        elif self.op == "&":
            return BiOp(self.left.to_strix(), '&&', self.right.to_strix())
        elif self.op == "|":
            return BiOp(self.left.to_strix(), '||', self.right.to_strix())
        # elif self.op == "W":
        #     return BiOp(BiOp(self.left, "U", self.right), "|", UniOp("G", self.left)).to_nuxmv()
        # elif self.op == "R":
        #     return BiOp(self.right, "W", BiOp(self.right, "&", self.left)).to_nuxmv()
        # elif self.op == "M":
        #     return BiOp(self.right, "U", BiOp(self.right, "&", self.left)).to_nuxmv()
        else:
            return BiOp(self.left.to_strix(), self.op, self.right.to_strix())

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
    def to_smt(self, symbol_table) -> (FNode, FNode):
        left_expr, left_invar = self.left.to_smt(symbol_table)
        right_expr, right_invar = self.right.to_smt(symbol_table)

        try:
            op = self.ops[self.op]
            return op(left_expr, right_expr), And(left_invar, right_invar)
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
        except Exception as e:
            print(str(e))
            op = self.ops[self.op]
            return op(left_expr, right_expr), And(left_invar, right_invar)

    def to_sympy(self):
        if self.op[0] == "|":
            return sympy.Or(self.left.to_sympy(), self.right.to_sympy())
        elif self.op[0] == "&":
            return sympy.And(self.left.to_sympy(), self.right.to_sympy())
        elif self.op[0] == "=" or self.op == "<->":
            return sympy.Equivalent(self.left.to_sympy(), self.right.to_sympy())
        else:
            raise Exception("Unsupported operator: " + self.op)

    def replace_math_exprs(self, symbol_table, cnt=0):
        if self.is_mathexpr(symbol_table):
                return Variable("math_" + str(cnt)), {("math_" + str(cnt)): self}
        else:
            new_left, dic_left = self.left.replace_math_exprs(symbol_table, cnt)
            new_right, dic_right = self.right.replace_math_exprs(symbol_table, cnt + len(dic_left))

            return BiOp(new_left, self.op, new_right), dic_left | dic_right

    def is_mathexpr(self, symbol_table):
        return isinstance(self.left, Value) and self.left.is_math_value() \
                or isinstance(self.right, Value) and self.right.is_math_value() \
                or isinstance(self.left, Variable) and not symbol_table[str(self.left)].type.lower().startswith("bool") \
                or isinstance(self.right, Variable) and not symbol_table[str(self.right)].type.lower().startswith("bool")

    def replace_formulas(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return BiOp(self.left.replace_formulas(context), self.op, self.right.replace_formulas(context))
        elif callable(context):
            ret = context(self)
            if ret is not None:
                return ret
            else:
                return BiOp(self.left.replace_formulas(context), self.op, self.right.replace_formulas(context))
        else:
            return BiOp(self.left.replace_formulas(context), self.op, self.right.replace_formulas(context))

    def prev_rep(self):
        if self.prev_representation is None:
            if self.op == ":=":
                self.prev_representation = BiOp(self.left, self.op, self.right.prev_rep())
            else:
                self.prev_representation = BiOp(self.left.prev_rep(), self.op, self.right.prev_rep())
        return self.prev_representation

    def replace_formulas_multiple(self, context: dict):
        if self in context.keys():
            return context[self]
        else:
            return [BiOp(l, self.op, r) for l in self.left.replace_formulas_multiple(context)
                                        for r in self.right.replace_formulas_multiple(context)]
