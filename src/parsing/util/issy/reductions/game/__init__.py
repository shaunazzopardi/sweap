"""Game-structure ISSY reductions."""

from .drop_unused_curr_input_snapshots import (
    drop_curr_input_snapshot_vars_if_no_minigames,
)

__all__ = [
    "drop_curr_input_snapshot_vars_if_no_minigames",
]
