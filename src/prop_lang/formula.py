import typing
from abc import ABC, abstractmethod
from typing import Any, TYPE_CHECKING, Self
from pysmt.fnode import FNode

if TYPE_CHECKING:
    from prop_lang.variable import Variable


class Formula(ABC):
    def __str__(self):
        return str(self)

    def __len__(self):
        return len(str(self))

    @abstractmethod
    def variablesin(self) -> typing.Iterable["Variable"]:
        pass

    @abstractmethod
    def simplify(self) -> Self:
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
    def to_nuxmv(self) -> str:
        pass

    @abstractmethod
    def to_strix(self) -> str:
        pass

    # TODO, keep a cache of this, so only done once
    @abstractmethod
    def to_smt(self, symbol_table: Any) -> tuple[FNode, FNode]:
        pass

    @abstractmethod
    def replace_math_exprs(self, symbol_table, cnt):
        pass

    def sub_formulas_up_to_associativity(self):
        return [self]

    @abstractmethod
    def to_sympy(self):
        pass

    @abstractmethod
    def prev_rep(self):
        pass

    def __add__(self, other):
        return str(self) + other
