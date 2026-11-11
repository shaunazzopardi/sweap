from typing import TYPE_CHECKING

from prop_lang.atom import Atom

if TYPE_CHECKING:
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

    def variablesin(self) -> list["Variable"]:
        return []

    def ops_used(self):
        return []

    def replace_formulas(self, context=None):
        return self

    def replace_math_exprs(self, context=None):
        return self

    def replace_vars(self, context=None):
        return self

    def simplify(self):
        return self

    def to_nuxmv(self):
        raise NotImplementedError("NonDeterministic.to_nuxmv")

    def to_smt(self):
        raise NotImplementedError("NonDeterministic.to_smt")

    def to_strix(self):
        raise NotImplementedError("NonDeterministic.to_strix")

    def to_sympy(self):
        raise NotImplementedError("NonDeterministic.to_sympy")

    def prev_rep(self):
        raise NotImplementedError("NonDeterministic.prev_rep")

    def replace_formulas_multiple(self, context: dict):
        return self

    def prev_rep(self):
        raise NotImplementedError("NonDeterministic.prev_rep")
