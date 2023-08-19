from enum import Enum

class LTLAbstractionBaseType(Enum):
    explicit_automaton = 1 # creates full unrolled automaton corresponding to predicate abstraction
    symbolic_predicate_representation = 2 # has some symbolic (succinct) representation of the predicate abstraction
    one_to_one_with_program = 3 # predicates for each atomic condition and action in program

class LTLAbstractionTransitionType(Enum):
    combined = 1 # combine con transitions with env transitions
    env_con_separate = 2 # keep con and env transitions separate

class LTLAbstractionStructureType(Enum):
    control_and_predicate_state = 1 # choose next depending on current control and predicate state
    control_state = 2 # choose next depending on current control state

class LTLAbstractionOutputType(Enum):
    after_env = 1 # only expose outputs after env steps
    everywhere = 2 # expose outputs after both con and env steps
