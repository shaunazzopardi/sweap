import re

from pysmt.fnode import FNode
from pysmt.shortcuts import Symbol, INT, BOOL, GE, LE, And, Int, TRUE

from programs.typed_valuation import TypedValuation
from prop_lang.atom import Atom


class Variable(Atom):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Variable):
            return self.name == other.name
        return NotImplemented

    def variablesin(self):
        return [self]

    def ground(self, context: [TypedValuation]):
        for val in context:
            if val.name == self.name:
                return val.value

        return self

    def simplify(self):
        return self

    def ops_used(self):
        return []

    def replace(self, context):
        if isinstance(context, list):
            for val in context:
                if (val.op == "=" or val.op == ":=") and (str(val.left.name) == self.name):
                    return val.right
        elif hasattr(context, '__call__'):
            return context(self)
        else:
            raise Exception("Variable.replace: context is not a list of assignments or a mapping function.")
        return self

    def to_nuxmv(self):
        return self

    def to_smt(self, symbol_table) -> (FNode, FNode):
        typed_val = symbol_table[self.name]

        if typed_val.type == "int" or typed_val.type == "integer":
            return Symbol(self.name, INT), TRUE()
        elif typed_val.type == "bool" or typed_val.type == "boolean":
            return Symbol(self.name, BOOL), TRUE()
        elif typed_val.type == "nat" or typed_val.type == "natural":
            return Symbol(self.name, INT), GE(Symbol(self.name, INT), Int(0))
        elif re.match("[0-9]+..+[0-9]+", typed_val.type):
            split = re.split("..+", typed_val.type)
            lower = split[0]
            upper = split[1]
            return Symbol(self.name, INT), And(GE(Symbol(self.name, INT), Int(lower)),
                                               LE(Symbol(self.name, INT), Int(upper)))
        else:
            raise NotImplementedError(f"Type {typed_val.type} unsupported.")

    def replace_math_exprs(self, symbol_table, cnt=0):
        return self, {}