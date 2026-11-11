from abc import ABC, abstractmethod

from analysis.abstraction.interface.predicate_abstraction import (
    PredicateAbstraction,
)


class AbstractionToLTL(ABC):
    @abstractmethod
    def __init__(self, program):
        pass

    @abstractmethod
    def abstraction_to_ltl(self, abstraction: PredicateAbstraction):
        pass
