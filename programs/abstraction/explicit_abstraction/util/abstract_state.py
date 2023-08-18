from prop_lang.formula import Formula
from prop_lang.util import neg, conjunct_formula_set, sat, conjunct


class AbstractState:
    def __init__(self, state, predicates: frozenset[Formula]):
        self.state = state
        self.predicates = sorted(list(predicates), key=lambda x: str(x))
        self.predicate_formula = conjunct_formula_set(self.predicates, sort=True)
        if any(p for p in self.predicates if neg(p) in self.predicates):
            raise ValueError("Abstract state cannot contain both p and !p: " + str(self))

    def __str__(self):
        return "(" + str(self.state) + ", " + ", ".join(map(str, self.predicates)) + ")"

    def __eq__(self, other):
        if isinstance(other, AbstractState):
            return self.state == other.state and self.predicate_formula == other.predicate_formula
        return NotImplemented

    def __hash__(self):
        return hash(self.state + str(self.predicate_formula))

    def unpack(self):
        return self.state, self.predicates

    def state(self):
        return self.state

    def predicates(self):
        return self.predicates

    def is_instance_of(self, other):
        if isinstance(other, AbstractState):
            return self.state == other.state and \
                frozenset(self.predicates).issubset(frozenset(other.predicates))
        return NotImplemented

    def compatible(self, other, symbol_table):
        if isinstance(other, AbstractState):
            return self.state == other.state and \
                sat(conjunct(self.predicate_formula, other.predicate_formula), symbol_table)
        return NotImplemented
