import functools
from typing import Union, Callable

import sympy
from pysmt.fnode import FNode
from pysmt.shortcuts import And, Or, Implies
from pysmt.shortcuts import (
    Plus,
    Minus,
    EqualsOrIff,
    LE,
    LT,
    GT,
    GE,
    NotEquals,
)
from sympy import Basic

import config
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import (
    Bi_ops_rels,
    BoolBiOps,
    MathOps,
    BoolUniOps,
    MathRels,
    bi_ops_rels_parser,
)
from prop_lang.types.types import BOOLEAN
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class BiOp(Formula):
    def __init__(self, left: Formula, op: Union[str, Bi_ops_rels], right: Formula):
        self.op = bi_ops_rels_parser(op) if isinstance(op, str) else op
        if self.op == MathOps.SUB:
            self.op = MathOps.ADD
            self.left = left
            if isinstance(right, UniOp) and right.op == MathOps.SUB:
                self.right = right.right
            else:
                self.right = UniOp(MathOps.SUB, right)
        else:
            self.left = left
            self.right = right

        self.vars = None

        self.prev_representation = None
        self.smt_representation = None
        self.hsh = hash(f"{self.left.__hash__()} {self.op} {self.right.__hash__()}")
        self.sub_formulas = self._sub_formulas_up_to_associativity()

    @functools.lru_cache()
    def __str__(self):
        if len(self.sub_formulas_up_to_associativity()) == 1:
            return (
                "(" + str(self.left) + " " + str(self.op) + " " + str(self.right) + ")"
            )
        else:
            return (
                "("
                + (" " + str(self.op) + " ").join(
                    [str(c) for c in self.sub_formulas_up_to_associativity()]
                )
                + ")"
            )

    def sub_formulas_up_to_associativity(self) -> list[Formula]:
        return self.sub_formulas

    def _sub_formulas_up_to_associativity(self) -> list[Formula]:
        if self.op in [BoolBiOps.CONJ, BoolBiOps.DISJ, MathOps.ADD]:
            is_same_as_op = lambda x: x == self.op
        else:
            return [self]

        sub_formulas = []
        if not isinstance(self.left, BiOp) or not is_same_as_op(self.left.op):
            sub_formulas += [self.left]
        else:
            sub_formulas += self.left.sub_formulas
        if not isinstance(self.right, BiOp) or not is_same_as_op(self.right.op):
            sub_formulas += [self.right]
        else:
            sub_formulas += self.right.sub_formulas
        return sub_formulas

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, BiOp):
            return (
                self.op == other.op
                and self.right == other.right
                and self.left == other.left
            )
        return False

    def __hash__(self):
        return self.hsh

    # returns list of variables that appear in formula
    # ordered as they appear in the formula
    # without already appearing variables
    @functools.lru_cache()
    def variablesin(self) -> list[Variable]:
        if self.vars is not None:
            return self.vars
        vars = self.left.variablesin() + self.right.variablesin()
        vars_unique = [v for (i, v) in enumerate(vars) if v not in vars[:i]]
        self.vars = vars_unique
        return vars_unique

    def simplify(self):
        left = self.left.simplify()
        right = self.right.simplify()
        if self.op is BoolBiOps.CONJ:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return left
            elif isinstance(right, Value) and right.is_true():
                return left
            elif isinstance(right, Value) and right.is_false():
                return right
        elif self.op is BoolBiOps.DISJ:
            if isinstance(left, Value) and left.is_true():
                return left
            elif isinstance(left, Value) and left.is_false():
                return right
            elif isinstance(right, Value) and right.is_true():
                return right
            elif isinstance(right, Value) and right.is_false():
                return left
        elif self.op is BoolBiOps.IMPL:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return Value(BoolAtoms.TRUE)
            elif isinstance(right, Value) and right.is_true():
                return Value(BoolAtoms.TRUE)
            elif isinstance(right, Value) and right.is_false():
                return UniOp(BoolUniOps.NEG, left)
        elif self.op is BoolBiOps.IFF:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return UniOp(BoolUniOps.NEG, right).simplify()
            elif isinstance(right, Value) and right.is_true():
                return left
            elif right == left:
                return Value(BoolAtoms.TRUE)
            elif isinstance(right, Value) and right.is_false():
                return UniOp("!", left).simplify()
        elif self.op is MathRels.EQ:
            if right == left:
                return Value(BoolAtoms.TRUE)
        return BiOp(left, self.op, right)

    @functools.lru_cache()
    def ops_used(self):
        return [self.op] + self.left.ops_used() + self.right.ops_used()

    def replace_vars(self, context):
        return BiOp(
            self.left.replace_vars(context),
            self.op,
            self.right.replace_vars(context),
        )

    @functools.lru_cache()
    def to_nuxmv(self):
        # if self.op == "%":
        #     return "toint(unsigned word[8](" + self.left.to_nuxmv() + ") mod unsigned word[8](" + self.right.to_nuxmv() + "))"
        # else:
        return (
            "(("
            + self.left.to_nuxmv()
            + ") "
            + self.op.to_nuxmv()
            + " ("
            + self.right.to_nuxmv()
            + "))"
        )

    @functools.lru_cache()
    def to_strix(self):
        return (
            "("
            + self.left.to_strix()
            + ") "
            + self.op
            + " ("
            + self.right.to_strix()
            + "))"
        )

    ops = {
        BoolBiOps.CONJ: And,
        BoolBiOps.DISJ: Or,
        BoolBiOps.IMPL: Implies,
        MathRels.EQ: EqualsOrIff,
        MathRels.NEQ: NotEquals,
        BoolBiOps.IFF: EqualsOrIff,
        MathRels.GT: GT,
        MathRels.GE: GE,
        MathRels.LT: LT,
        MathRels.LE: LE,
        MathOps.ADD: Plus,
        MathOps.SUB: Minus,
        # "*": Times,
        # "/": Div,
        # "%": BVSRem,
    }

    def to_smt(self, symbol_table) -> tuple[FNode, FNode]:
        cache = config.Config.getConfig().cache_smt
        if cache and self.smt_representation:
            return self.smt_representation

        left_expr, left_invar = self.left.to_smt(symbol_table)
        right_expr, right_invar = self.right.to_smt(symbol_table)

        try:
            op = self.ops[self.op]
            f = op(left_expr, right_expr), And(left_invar, right_invar)
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
        except Exception as e:
            print(str(e))
            op = self.ops[self.op]
            f = op(left_expr, right_expr), And(left_invar, right_invar)
        if cache:
            self.smt_representation = f

        return f

    def to_sympy(self) -> Basic:
        if self.op == BoolBiOps.DISJ:
            return sympy.Or(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == BoolBiOps.CONJ:
            return sympy.And(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathRels.EQ or self.op == BoolBiOps.IFF:
            return sympy.Equivalent(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathRels.GT:
            return sympy.StrictGreaterThan(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathRels.LT:
            return sympy.StrictLessThan(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathRels.GE:
            return sympy.GreaterThan(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathRels.LE:
            return sympy.LessThan(self.left.to_sympy(), self.right.to_sympy())
        elif self.op == MathOps.SUB:
            return sympy.Add(
                self.left.to_sympy(),
                sympy.Mul(sympy.Integer(-1), self.right.to_sympy()),
            )
        elif self.op == MathOps.ADD:
            return sympy.Add(
                self.left.to_sympy(),
                self.right.to_sympy(),
            )
        else:
            raise Exception("Unsupported operator: " + self.op)

    def replace_math_exprs(
        self, symbol_table, cnt=0
    ) -> tuple[Formula, dict[str, Formula]]:
        if self.is_mathexpr(symbol_table):
            return Variable("math_" + str(cnt)), {("math_" + str(cnt)): self}
        else:
            new_left, dic_left = self.left.replace_math_exprs(symbol_table, cnt)
            new_right, dic_right = self.right.replace_math_exprs(
                symbol_table, cnt + len(dic_left)
            )

            return BiOp(new_left, self.op, new_right), dic_left | dic_right

    def is_mathexpr(self, symbol_table) -> bool:
        return (
            isinstance(self.left, Value)
            and self.left.is_math_value()
            or isinstance(self.right, Value)
            and self.right.is_math_value()
            or isinstance(self.left, Variable)
            and not symbol_table[str(self.left)] == BOOLEAN
            or isinstance(self.right, Variable)
            and not symbol_table[str(self.right)] == BOOLEAN
        )

    def replace_formulas(
        self, context: Union[dict[Formula, Formula], Callable[[Formula], Formula]]
    ) -> Formula:
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return BiOp(
                    self.left.replace_formulas(context),
                    self.op,
                    self.right.replace_formulas(context),
                )
        elif callable(context):
            ret = context(self)
            if ret is not None:
                return ret
            else:
                return BiOp(
                    self.left.replace_formulas(context),
                    self.op,
                    self.right.replace_formulas(context),
                )
        else:
            return BiOp(
                self.left.replace_formulas(context),
                self.op,
                self.right.replace_formulas(context),
            )

    def prev_rep(self) -> Formula:
        if self.prev_representation is None:
            self.prev_representation = BiOp(
                self.left.prev_rep(), self.op, self.right.prev_rep()
            )
        return self.prev_representation

    def replace_formulas_multiple(
        self, context: dict[Formula, list[Formula]]
    ) -> list[Formula]:
        if self in context.keys():
            return context[self]
        else:
            return [
                BiOp(l, self.op, r)
                for l in self.left.replace_formulas_multiple(context)
                for r in self.right.replace_formulas_multiple(context)
            ]
