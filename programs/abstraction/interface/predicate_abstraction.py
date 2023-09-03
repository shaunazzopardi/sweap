from abc import ABC, abstractmethod

from programs.abstraction.interface.ltl_abstraction_type import LTLAbstractionType
from programs.program import Program
from programs.synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula


class PredicateAbstraction(ABC):

    @abstractmethod
    def __init__(self, program: Program):
        pass

    @abstractmethod
    def add_predicates(self,
                       new_interpolants: [Formula],
                       new_ranking_and_invars: dict[Formula, [Formula]],
                       structural_loop_env):
        pass

    @abstractmethod
    def concretise_counterexample(self, counterexample: [dict]):
        pass

    @abstractmethod
    def to_automaton_abstraction(self):
        pass

    # @abstractmethod
    # def to_ltl(self,
    #            original_ltl_problem: LTLSynthesisProblem,
    #            ltlAbstractionType: LTLAbstractionType) -> tuple[object, LTLSynthesisProblem]:
    #     pass

    @abstractmethod
    def massage_mealy_machine(self,
                              mealymachine,
                              base_abstraction,
                              ltlAbstractionType,
                              synthesis_problem,
                              controller: bool):
        pass

    @abstractmethod
    def get_state_predicates(self) -> [Formula]:
        pass

    @abstractmethod
    def get_transition_predicates(self) -> [Formula]:
        pass

    @abstractmethod
    def get_interpolants(self) -> [Formula]:
        pass

    @abstractmethod
    def get_ranking_and_invars(self) -> dict[Formula, [Formula]]:
        pass

    def get_all_preds(self):
        return self.get_state_predicates() + self.get_transition_predicates()

    @abstractmethod
    def get_program(self) -> Program:
        pass

    @abstractmethod
    def get_symbol_table(self) -> dict[str, TypedValuation]:
        pass
