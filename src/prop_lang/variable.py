import re

import sympy.core.symbol
from pysmt.fnode import FNode
from pysmt.shortcuts import INT, BOOL, GE, LE, And, Int, TRUE, Symbol

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

    def replace_vars(self, context):
        if isinstance(context, list):
            for val in context:
                if (val.op == "=" or val.op == ":=") and (str(val.left.name) == self.name):
                    return val.right
        elif hasattr(context, '__call__'):
            return context(self)
        else:
            try:
                val = context
                if (val.op == "=" or val.op == ":=") and (str(val.left.name) == self.name):
                    return val.right
            except:
                raise Exception("Variable.replace: context is not a list of assignments, an assignment, or a mapping function.")
        return self

    def to_nuxmv(self):
        return self

    def to_strix(self):
        return self

    def to_smt(self, symbol_table) -> (FNode, FNode):
        if self.name in symbol_table.keys():
            typed_val = symbol_table[self.name]
        elif self.name.split("_prev")[0] in symbol_table.keys():
            typed_val = symbol_table[self.name.split("_prev")[0]]
        else:
            raise Exception("Variable.to_smt: variable " + self.name + " not in symbol table.")

        if typed_val.type == "int" or typed_val.type == "integer":
            return Symbol(self.name, INT), TRUE()
        elif typed_val.type == "bool" or typed_val.type == "boolean":
            return Symbol(self.name, BOOL), TRUE()
        elif typed_val.type == "nat" or typed_val.type == "natural":
            return Symbol(self.name, INT), GE(Symbol(self.name, INT), Int(0))
        elif re.match("[0-9]+..+[0-9]+", typed_val.type):
            split = re.split("\\.\\.+", typed_val.type)
            lower = int(split[0])
            upper = int(split[1])
            return Symbol(self.name, INT), And(GE(Symbol(self.name, INT), Int((lower))),
                                               LE(Symbol(self.name, INT), Int((upper))))
        else:
            raise NotImplementedError(f"Type {typed_val.type} unsupported.")

    def replace_math_exprs(self, symbol_table, cnt=0):
        return self, {}

    def to_sympy(self):
        return sympy.core.symbol.Symbol(self.name)

    def replace_formulas(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            else:
                return self
        elif callable(context):
            if context(self) is not None:
                return context(self)
            else:
                return self
