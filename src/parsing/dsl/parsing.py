#!/usr/bin/env python3


from enum import Enum

from pysmt.fnode import FNode
from pysmt.shortcuts import Symbol, get_free_variables, get_type, substitute
from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable
from parsing.dsl.grammar import GRAMMAR
from parsing.string_to_ltl import string_to_ltl


def remove_version(var):
    return Symbol(var.symbol_name().split("#")[0], get_type(var))


def remove_all_versions(formula):
    fvs = get_free_variables(formula)
    return substitute(formula, {fv: remove_version(fv) for fv in fvs})


class Token(Enum):
    ADD     = "+"
    SUB     = "-"
    MUL     = "*"
    DIV     = "/"
    GT      = ">"
    LT      = "<"
    GE      = ">="
    LE      = "<="
    EQ      = "=="
    NE      = "!="
    AND     = "&&"
    OR      = "||"
    IMPL    = "->"
    NOT     = "!"


class BaseNode(Node):
    def unparse(self) -> str:
        raise NotImplementedError()


class MethodModality(Enum):
    F       = "F"
    GF      = "GF"
    notFG    = "!FG"

    def to_ltl(self):
        return " ".join(self.value)


class Store(BaseNode):
    name = None


class Expr(BaseNode):
    pass


class Literal(Expr):
    value = None

    def get_type(self):
        return "bool" if isinstance(self.value, bool) else "int"


class Load(Expr):
    name = None


class Operation(Expr):
    def __init__(self, ast=None, **attributes):
        super().__init__(ast, **attributes)
        self.op = Token(self.op)


class BinOp(Operation):
    left: Expr = None
    op = None
    right: Expr = None


class Increment(BaseNode):
    var_name = None


class Decrement(BaseNode):
    var_name = None


class UnaryOp(Operation):
    op = None
    expr: Expr = None


class Comparison(BinOp):
    pass


class BinLogic(BinOp):
    pass


class If(BaseNode):
    cond = None
    body = None
    or_else = None


class Assign(BaseNode):
    lhs: Store = None
    rhs = None

    def __repr__(self) -> str:
        return self.unparse()

    def __str__(self):
        return self.unparse()

    def unparse(self) -> str:
        return f"{self.lhs} := {self.rhs};"


class Decl(BaseNode):
    var_type = None
    var_name = None
    init = None
    io = None


class EnumDef(BaseNode):
    name = None
    values = None


class MethodDef(BaseNode):
    name = None
    kind = None
    modalities = None
    params = None
    assumes = None
    asserts = None
    decls = None
    body = None

    def __init__(self, ast=None, **attributes):
        global CONTEXT
        super().__init__(ast, **attributes)
        self.modalities = [MethodModality(m) for m in self.modalities]
        CONTEXT = self


class Program(BaseNode):
    decls = None
    enums = None
    methods = None
    assumes: str = None
    guarantees: str = None

    def __init__(self, ast=None, **attributes):
        super().__init__(ast, **attributes)
        if self.assumes:
            assumes = (x.strip() for a in self.assumes for x in a.split(";"))
            self.assumes = tuple(string_to_ltl(x) for x in assumes if x)

        if self.guarantees:
            guarantees = (x.strip() for a in self.guarantees for x in a.split(";"))  # noqa: E501
            self.guarantees = tuple(string_to_ltl(x) for x in guarantees if x)



def to_formula(expr: FNode):
    tests_biop = {
        "+": expr.is_plus,
        "-": expr.is_minus,
        "*": expr.is_times,
        "/": expr.is_div,
        "<=": expr.is_le,
        "<": expr.is_lt,
        "==": expr.is_equals,
        "<->": expr.is_iff,
        "->": expr.is_implies,
        "&&": expr.is_and,
        "||": expr.is_or,
    }

    for op, test in tests_biop.items():
        if test():
            new_expr = None
            for arg in expr.args():
                if new_expr is None:
                    new_expr = to_formula(arg)
                    continue
                new_expr = BiOp(new_expr, op, to_formula(arg))
            return new_expr

    if expr.is_constant():
        return Value(str(expr))

    if expr.is_symbol():
        return Variable(expr.symbol_name())
    elif expr.is_not():
        return UniOp("!", to_formula(expr.arg(0)))

    # We've tried so hard & got so far
    raise NotImplementedError(expr, expr.node_type())


def parse_dsl(code: str) -> BaseNode:
    dsl_parser: Grammar = compile(GRAMMAR)
    __semantics = ModelBuilderSemantics(types=[
        t for t in globals().values()
        if type(t) is type and issubclass(t, BaseNode)])
    return dsl_parser.parse(code, semantics=__semantics)
