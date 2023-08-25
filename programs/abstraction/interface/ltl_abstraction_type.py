from enum import Enum

class LTLAbstractionBaseType(Enum):
    explicit_automaton = 1  # creates full unrolled automaton corresponding to predicate abstraction
    symbolic_predicate_representation = 2  # has some symbolic (succinct) representation of the predicate abstraction
    one_to_one_with_program = 3  # predicates for each atomic condition and action in program


class LTLAbstractionTransitionType(Enum):
    combined = 1  # combine con transitions with env transitions
    env_con_separate = 2  # keep con and env transitions separate


class LTLAbstractionStructureType(Enum):
    control_and_predicate_state = 1  # choose next depending on current control and predicate state
    control_state = 2  # choose next depending on current control state


class LTLAbstractionOutputType(Enum):
    after_env = 1  # only expose outputs after env steps
    everywhere = 2  # expose outputs after both con and env steps


class LTLAbstractionType:
    base_type: LTLAbstractionBaseType
    transition_type: LTLAbstractionTransitionType
    structure_type: LTLAbstractionStructureType
    output_type: LTLAbstractionOutputType

    def __init__(self,
                 base_type: LTLAbstractionBaseType,
                 transition_type: LTLAbstractionTransitionType,
                 structure_type: LTLAbstractionStructureType,
                 output_type: LTLAbstractionOutputType):
        self.base_type = base_type
        self.transition_type = transition_type
        self.structure_type = structure_type
        self.output_type = output_type

    def __str__(self):
        return (str(self.base_type) + ", " +
                str(self.transition_type) + ", " +
                str(self.structure_type) + ", " +
                str(self.output_type))

