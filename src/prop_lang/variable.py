import sympy.core.symbol

from pysmt.fnode import FNode

import config
from prop_lang.atom import Atom
from prop_lang.types.types import typed_var_to_pysmt_type


class Variable(Atom):
    def __init__(self, name: str):
        self.name = name
        self.prev_representation = None
        self.smt_representation = None

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

    def simplify(self):
        return self

    def ops_used(self):
        return []

    def replace_vars(self, context):
        if isinstance(context, dict):
            if self in context.keys():
                return context[self]
            elif self.name in context.keys():
                return context[self.name]
            else:
                return self
        elif hasattr(context, "__call__"):
            return context(self)
        else:
            raise Exception(
                "Variable.replace: context is not a dictionary or a function."
            )

    def to_nuxmv(self):
        if self.is_next():
            return "next(" + self.name[:-1] + ")"
        else:
            return self.name

    def to_strix(self):
        return self.name

    def to_smt(self, symbol_table) -> tuple[FNode, FNode]:
        cache = config.Config.getConfig().cache_smt

        if cache and self.smt_representation:
            return self.smt_representation
        if self.name in symbol_table.keys():
            type = symbol_table[self.name]
        elif self.name.split("_prev")[0] in symbol_table.keys():
            type = symbol_table[self.name.split("_prev")[0]]
        elif self.is_next():
            type = symbol_table[self.prev_rep().name]
        else:
            raise Exception(
                "Variable.to_smt: variable " + self.name + " not in symbol table."
            )

        f = typed_var_to_pysmt_type(self.name, type)
        if cache:
            self.smt_representation = f
        return f

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
            ret = context(self)
            if ret is not None:
                return ret
            else:
                return self
        else:
            return self

    def replace_formulas_multiple(self, context: dict):
        if self in context.keys():
            return context[self]
        else:
            return [self]

    def prev_rep(self):
        if self.prev_representation is None:
            if self.is_next():
                self.prev_representation = Variable(self.name[:-1])
            else:
                self.prev_representation = Variable(self.name + "_prev")
        return self.prev_representation

    def is_next(self):
        return self.name.endswith("'")
