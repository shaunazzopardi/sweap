from abc import ABC, abstractmethod
from typing import Optional

from graphviz import Digraph

from prop_lang.formula import Formula


class Machine(ABC):

    @abstractmethod
    def add_transitions(self, trans_dict: dict, symbol_table: dict):
        pass

    @abstractmethod
    def to_dot(self, pred_list: Optional[list[Formula]] = None) -> Digraph:
        pass
