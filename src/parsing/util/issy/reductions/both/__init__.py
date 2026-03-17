"""ISSY reductions that affect both game and LTL structure."""

from .next_state_var_booleanisation import (
    _promote_next_state_vars_to_controller_props,
)

__all__ = [
    "_promote_next_state_vars_to_controller_props",
]
