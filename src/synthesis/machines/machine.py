from abc import ABC, abstractmethod
from prop_lang.formula import Formula


class Machine(ABC):

    def add_transitions(self, trans_dict: dict, symbol_table: dict):
        pass

    @abstractmethod
    def to_dot(self, pred_list: [Formula] = None):
        pass

    @abstractmethod
    def to_nuXmv_with_turns(
        self, prog_states, prog_out_events, state_pred_list, trans_pred_list
    ):
        pass
