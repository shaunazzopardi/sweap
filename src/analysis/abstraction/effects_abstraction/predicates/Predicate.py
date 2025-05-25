from abc import ABC, abstractmethod

from prop_lang.formula import Formula
from prop_lang.util import conjunct, sat
from prop_lang.variable import Variable


class Predicate(ABC):
    @abstractmethod
    def variablesin(self):
        pass

    @abstractmethod
    def boolean_rep(self):
        pass

    @abstractmethod
    def extend_effect_now(
        self,
        gu: Formula,
        effect: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        pass

    @abstractmethod
    def extend_effect_next(
        self,
        gu: Formula,
        effect: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        pass

    @abstractmethod
    def extend_effect(
        self,
        gu: Formula,
        effect: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        pass

    @abstractmethod
    def is_pre_cond(self, gu: Formula, symbol_table):
        pass

    @abstractmethod
    def is_invar(self, gu: Formula, symbol_table):
        pass

    @abstractmethod
    def is_post_cond(self, gu: Formula, symbol_table):
        pass


def refine_nexts(now, nexts, symbol_table):
    new_nexts = []
    for v_next in nexts:
        if sat(conjunct(now, v_next), symbol_table):
            new_nexts.append(v_next)
    return new_nexts
