"""Drop implication objectives with UNSAT initial-state antecedents."""

import logging

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (
    extract_initial_formula,
    sat,
)


def drop_formula_objectives_with_unsat_initial_antecedents(
    formula_objectives: list[Formula],
    symbol_table,
    *,
    raise_if_all_removed: bool = True,
) -> tuple[list[Formula], list[tuple[Formula, Formula]]]:
    remaining = []
    removed = []
    for q in formula_objectives:
        if isinstance(q, BiOp) and str(q.op) == "->":
            antecedent = q.left
            antecedent_init = extract_initial_formula(antecedent)
            if antecedent_init is not None and str(antecedent_init) == str(antecedent):
                if not sat(antecedent, symbol_table):
                    removed.append((q, antecedent))
                    continue
        remaining.append(q)

    if len(removed) > 0:
        for objective, antecedent in removed:
            logging.info(
                "Dropping trivially-satisfied implication objective with UNSAT initial antecedent: %s (antecedent=%s)",
                objective,
                antecedent,
            )
    if len(remaining) == 0 and len(removed) > 0 and raise_if_all_removed:
        raise Exception(
            "Specification is trivially UNSAT: all implication assumptions are unsatisfiable in the initial state."
        )
    return remaining, removed
