from abc import ABC, abstractmethod

from programs.abstraction.interface.ltl_abstraction_types import LTLAbstractionBaseType, LTLAbstractionTransitionType, \
    LTLAbstractionStructureType
from programs.program import Program
from prop_lang.formula import Formula


class PredicateAbstraction(ABC):

    @abstractmethod
    def __init__(self, program: Program):
        pass

    @abstractmethod
    def add_predicates(self, state_predicates: [Formula], transition_predicates: [Formula]):
        pass

    @abstractmethod
    def concretise_counterexample(self, counterexample: [dict]):
        pass

    @abstractmethod
    def to_explicit_abstraction(self):
        pass

    @abstractmethod
    def to_ltl(self, base_type: LTLAbstractionBaseType,
                     transition_type: LTLAbstractionTransitionType,
                     structure_type: LTLAbstractionStructureType) -> tuple[object, [Formula]]:
        pass

    @abstractmethod
    def massage_mealy_machine(self, mealymachine):
        pass

    @abstractmethod
    def get_state_predicates(self) -> [Formula]:
        pass

    @abstractmethod
    def get_transition_predicates(self) -> [Formula]:
        pass

    @abstractmethod
    def get_program(self) -> Program:
        pass