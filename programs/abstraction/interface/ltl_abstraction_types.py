from enum import Enum

class LTLAbstractionBaseType(Enum):
    explicit = 1
    symbolic = 2

class LTLAbstractionTransitionType(Enum):
    combined = 1
    env_con_separate = 2

class LTLAbstractionStructureType(Enum):
    predicate_state = 1
