"""ISSY reduction passes."""

from .game import (
    drop_curr_input_snapshot_vars_if_no_minigames,
)
from .both import (
    _promote_next_state_vars_to_controller_props,
)
from .ltl import (
    drop_formula_objectives_with_unsat_initial_antecedents,
)

__all__ = [
    "drop_curr_input_snapshot_vars_if_no_minigames",
    "drop_formula_objectives_with_unsat_initial_antecedents",
    "_promote_next_state_vars_to_controller_props",
]
