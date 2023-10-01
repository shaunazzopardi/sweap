import re

import sympy
from pysmt.fnode import FNode
from pysmt.shortcuts import Int, TRUE, FALSE

from programs.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.variable import Variable


class NonDeterministic(Atom):
    def __init__(self):
        self.name = "*"

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, NonDeterministic):
            return True
        return NotImplemented

    def variablesin(self) -> [Variable]:
        return []

    def ops_used(self):
        return []

    def ground(self):
        raise NotImplementedError("NonDeterministic.ground")

    def replace_formulas(self):
        raise NotImplementedError("NonDeterministic.replace_formulas")

    def replace_math_exprs(self):
        raise NotImplementedError("NonDeterministic.replace_math_exprs")

    def replace_vars(self):
        raise NotImplementedError("NonDeterministic.replace_vars")

    def simplify(self):
        raise NotImplementedError("NonDeterministic.simplify")

    def to_nuxmv(self):
        raise NotImplementedError("NonDeterministic.to_nuxmv")

    def to_smt(self):
        raise NotImplementedError("NonDeterministic.to_smt")

    def to_strix(self):
        raise NotImplementedError("NonDeterministic.to_strix")

    def to_sympy(self):
        raise NotImplementedError("NonDeterministic.to_sympy")