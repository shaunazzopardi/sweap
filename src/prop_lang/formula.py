from abc import ABC, abstractmethod
from typing import Any
from pysmt.fnode import FNode
from programs.typed_valuation import TypedValuation


class Formula(ABC):
    @abstractmethod
    def __str__(self):
        pass

    def __len__(self):
        return len(str(self))

    @abstractmethod
    def variablesin(self):
        pass

    @abstractmethod
    def ground(self, context: [TypedValuation]):
        pass

    @abstractmethod
    def simplify(self):
        pass

    @abstractmethod
    def ops_used(self):
        pass

    # contexts assumed to be a list of assignments
    @abstractmethod
    def replace_vars(self, context):
        pass

    def replace(self, context):
        return self.replace_vars(context)

    # contexts assumed to be a list of assignments or dicts
    @abstractmethod
    def replace_formulas(self, context: dict):
        pass

    @abstractmethod
    def replace_formulas_multiple(self, context: dict):
        pass

    @abstractmethod
    def to_nuxmv(self):
        pass

    @abstractmethod
    def to_strix(self):
        pass

    # TODO, keep a cache of this, so only done once
    @abstractmethod
    def to_smt(self, symbol_table: Any) -> (FNode, FNode):
        pass

    @abstractmethod
    def replace_math_exprs(self, cnt):
        pass

    def sub_formulas_up_to_associativity(self):
        return [self]

    @abstractmethod
    def to_sympy(self):
        pass

    @abstractmethod
    def prev_rep(self):
        pass
