import re
from typing import Union

import sympy
from pysmt.fnode import FNode

from pysmt.shortcuts import Int, TRUE, FALSE
from prop_lang.atom import Atom
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.variable import Variable


class Value(Atom):
    def __init__(self, val: Union[BoolAtoms, int]):
        self.val = val

    def __str__(self):
        return str(self.val)

    def __hash__(self):
        return self.val.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Value):
            return self.val == other.val
        return NotImplemented

    def is_true(self):
        return self.val == BoolAtoms.TRUE

    def is_false(self):
        return self.val == BoolAtoms.FALSE

    def variablesin(self) -> [Variable]:
        return []

    def simplify(self):
        return self

    def ops_used(self):
        return []

    def replace_vars(self, context):
        return self

    def to_nuxmv(self):
        if self.is_true():
            return "TRUE"
        elif self.is_false():
            return "FALSE"
        else:
            return str(self.val)

    def to_strix(self):
        if self.is_true():
            return "true"
        elif self.is_false():
            return "false"
        else:
            return str(self.val)

    def to_smt(self, _) -> (FNode, FNode):
        if self.is_true():
            return TRUE(), TRUE()
        elif self.is_false():
            return FALSE(), TRUE()
        else:
            try:
                return Int(int(self.val)), TRUE()
            except:
                raise Exception(
                    "Value.to_smt: Value is not an integer: " + str(self.val)
                )

    def replace_math_exprs(self, symbol_table, cnt=0):
        if not self.is_true() and not self.is_false():
            raise Exception("Dangling numerical value: " + str(self))
        return self, {}

    def is_math_value(self):
        return re.match("[0-9]+", str(self.val))

    def to_sympy(self):
        return sympy.core.symbol.Symbol(str(self.val))

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

    def prev_rep(self):
        return self

    def replace_formulas_multiple(self, context: dict):
        return [self]

    def type(self):
        if self.is_true() or self.is_false():
            return BOOLEAN
        elif re.match("[0-9]+", str(self.val)):
            return INTEGER
        else:
            raise Exception(
                "Value.type: Value is not a boolean or integer: " + self.val
            )
