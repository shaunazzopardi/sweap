from prop_lang.formula import Formula


class AbstractState:
    def __init__(self, state, predicates: frozenset[Formula]):
        self.state = state
        self.predicates = sorted(list(predicates), key=lambda x: str(x))

    def __str__(self):
        return "(" + str(self.state) + ", " + ", ".join(map(str, self.predicates)) + ")"

    def __eq__(self, other):
        if isinstance(other, AbstractState):
            return self.state == other.state and frozenset(self.predicates) == frozenset(other.predicates)
        return NotImplemented

    def __hash__(self):
        return hash(frozenset((hash(self.state), frozenset(self.predicates))))

    def unpack(self):
        return self.state, self.predicates

    def state(self):
        return self.state

    def predicates(self):
        return self.predicates
