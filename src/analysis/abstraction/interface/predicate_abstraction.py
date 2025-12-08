from abc import ABC, abstractmethod

from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.types.types import Type


class PredicateAbstraction(ABC):
    @abstractmethod
    def __init__(self, program: Program):
        pass

    @abstractmethod
    def add_predicates(
        self,
        new_interpolants: list[Formula],
        new_ranking_and_invars: dict[Formula, list[Formula]],
        structural_loop_env,
    ):
        pass

    @abstractmethod
    def concretise_counterexample(self, counterexample: list[dict]):
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
    def get_state_predicates(self) -> list[Formula]:
        pass

    @abstractmethod
    def get_transition_predicates(self) -> list[Formula]:
        pass

    @abstractmethod
    def get_interpolants(self) -> list[Formula]:
        pass

    @abstractmethod
    def get_ranking_and_invars(self) -> dict[Formula, list[Formula]]:
        pass

    @abstractmethod
    def get_all_preds(self):
        pass

    @abstractmethod
    def get_program(self) -> Program:
        pass

    @abstractmethod
    def get_symbol_table(self) -> dict[str, Type]:
        pass
