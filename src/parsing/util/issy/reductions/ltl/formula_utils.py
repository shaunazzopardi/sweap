from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    extract_initial_formula,
    implies,
    is_tautology,
    put_next_vars_on_left_side,
    put_vars_on_left_side,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

_TEMPORAL_OPS = {"X", "F", "G", "U", "W", "R", "M"}


def canonicalize_relational_atom_vars_left(q: Formula) -> Formula | None:
    if not isinstance(q, BiOp):
        return None
    if str(q.op) not in {"=", "!=", "<", "<=", ">", ">="}:
        return None
    vars_here = [v for v in q.variablesin() if isinstance(v, Variable)]
    if len(vars_here) == 0:
        return None

    has_next_var = any(v.is_next() for v in vars_here)
    if has_next_var:
        _, normalised = put_next_vars_on_left_side(q)
    else:
        _, normalised = put_vars_on_left_side(q)
    return normalised


def is_canonical(left: Formula, right: Formula, var_name: str) -> bool:
    """Check if left=right is in canonical form."""
    return (
        isinstance(left, Variable)
        and left.is_next()
        and left.prev_rep().name == var_name
        and not any(
            v for v in right.variablesin() if isinstance(v, Variable) and v.is_next()
        )
    )


def canonicalize_formula_relations_vars_left(formula: Formula) -> Formula:
    return formula.replace_formulas(
        lambda node: canonicalize_relational_atom_vars_left(node)
    )


def extract_formula_only_initial_assumptions(
    formula_objective: Formula,
) -> Formula | None:
    def _collect_initial_assumption_candidates(q: Formula) -> list[Formula]:
        candidates = []
        if isinstance(q, BiOp) and q.op == "&":
            candidates.extend(_collect_initial_assumption_candidates(q.left))
            candidates.extend(_collect_initial_assumption_candidates(q.right))
            return candidates
        if isinstance(q, BiOp) and q.op == "->":
            candidate = q.left
            init_formula = extract_initial_formula(candidate)
            if init_formula is not None and str(init_formula) == str(candidate):
                candidates.append(candidate)
            return candidates
        candidate = q
        init_formula = extract_initial_formula(candidate)
        if init_formula is not None and str(init_formula) == str(candidate):
            candidates.append(candidate)
        return candidates

    init_assumptions = _collect_initial_assumption_candidates(formula_objective)

    if len(init_assumptions) == 0:
        return None
    return conjunct_formula_set(init_assumptions)


def extract_common_formula_only_initial_assumptions(
    formula_objectives: list[Formula],
) -> Formula | None:
    if len(formula_objectives) == 0:
        return None

    def _flatten_conjuncts(q: Formula) -> list[Formula]:
        if isinstance(q, BiOp) and q.op == "&":
            return _flatten_conjuncts(q.left) + _flatten_conjuncts(q.right)
        return [q]

    per_objective_parts = []
    for objective in formula_objectives:
        init_formula = extract_formula_only_initial_assumptions(objective)
        if init_formula is None:
            return None
        parts = _flatten_conjuncts(init_formula)
        if len(parts) == 0:
            return None
        per_objective_parts.append({str(p): p for p in parts})

    common_keys = set(per_objective_parts[0].keys())
    for part_map in per_objective_parts[1:]:
        common_keys.intersection_update(part_map.keys())

    if len(common_keys) == 0:
        return None

    representative_map = per_objective_parts[0]
    common_parts = [representative_map[k] for k in sorted(common_keys)]
    return conjunct_formula_set(common_parts)


def merge_shared_antecedent_implications(
    formulas: list[Formula],
) -> Formula | None:
    if len(formulas) <= 1:
        return None
    implications = []
    for q in formulas:
        if not isinstance(q, BiOp) or q.op != "->":
            return None
        implications.append(q)

    first_assumption = implications[0].left
    for imp in implications[1:]:
        if imp.left != str(first_assumption):
            return None

    return BiOp(
        first_assumption,
        "->",
        conjunct_formula_set([imp.right for imp in implications]),
    )


def formula_only_assumptions_are_initial_or_none(
    formula_objectives: list[Formula],
) -> bool:
    def _flatten_conjuncts(q: Formula) -> list[Formula]:
        if isinstance(q, BiOp) and q.op == "&":
            return _flatten_conjuncts(q.left) + _flatten_conjuncts(q.right)
        return [q]

    initial_antecedents = []
    for q in formula_objectives:
        if not isinstance(q, BiOp) or q.op != "->" or len(q.left.variablesin()) == 0:
            continue
        left_ops = q.left.ops_used()
        # check if any op used is an LTL op
        if any(op in {"X", "G", "F", "U", "R"} for op in left_ops):
            return False
        antecedent = q.left
        initial_antecedents.append(antecedent)

    if len(initial_antecedents) > 1:
        common_parts = {str(p) for p in _flatten_conjuncts(initial_antecedents[0])}
        for antecedent in initial_antecedents[1:]:
            common_parts.intersection_update(
                {str(p) for p in _flatten_conjuncts(antecedent)}
            )
            if len(common_parts) == 0:
                return False
    return True


def program_enforced_initial_formula(program: Program) -> Formula | None:
    if len(program.init_var_values) == 0:
        return None
    init_equalities = []
    for var_name in sorted(program.init_var_values.keys()):
        if var_name not in program.symbol_table:
            continue
        init_equalities.append(
            BiOp(Variable(var_name), "=", program.init_var_values[var_name])
        )
    if len(init_equalities) == 0:
        return None
    return conjunct_formula_set(init_equalities)


def is_safety_or_reachability_objective(formula: Formula) -> bool:
    f = formula
    if isinstance(f, UniOp) and f.op in {"G", "F"}:
        return True
    if isinstance(f, BiOp) and f.op == "&":
        return is_safety_or_reachability_objective(
            f.left
        ) and is_safety_or_reachability_objective(f.right)
    if isinstance(f, Value) and isinstance(f.val, BoolAtoms):
        return True
    return False


def strip_consumed_initial_assumptions_from_objectives(
    formula_objectives: list[Formula],
    enforced_initial_formula: Formula | None,
    symbol_table,
) -> tuple[list[Formula], int]:
    if enforced_initial_formula is None:
        return formula_objectives, 0

    def _try_strip_top_level_implication(q: Formula) -> tuple[Formula, int]:
        if not isinstance(q, BiOp) or q.op != "->":
            return q, 0
        antecedent = q.left
        antecedent_init = extract_initial_formula(antecedent)
        if (
            antecedent_init is not None
            and str(antecedent_init) == str(antecedent)
            and is_tautology(
                implies(enforced_initial_formula, antecedent), symbol_table
            )
        ):
            return q.right, 1
        return q, 0

    def _rewrite_formula(q: Formula) -> tuple[Formula, int]:
        if isinstance(q, BiOp) and q.op == "&":
            new_left, removed_left = _rewrite_formula(q.left)
            new_right, removed_right = _rewrite_formula(q.right)
            if removed_left + removed_right == 0:
                return q, 0
            return BiOp(new_left, q.op, new_right), removed_left + removed_right
        return _try_strip_top_level_implication(q)

    rewritten = []
    removed = 0
    for objective in formula_objectives:
        rewritten_obj, removed_here = _rewrite_formula(objective)
        rewritten.append(rewritten_obj)
        removed += removed_here
    return rewritten, removed


def reduce_formula_set_up_to_equivalence(
    formulas: set[Formula], symbol_table
) -> set[Formula]:
    # reduce a set of formulas up to equivalence
    # and, if there is a formula that is stronger than the other, than keep the weaker formula
    reduced = set()
    for f in formulas:
        is_stronger = False
        to_remove = set()
        for r in reduced:
            f_stronger = is_tautology(implies(f, r), symbol_table)
            r_stronger = is_tautology(implies(r, f), symbol_table)
            if f_stronger:
                is_stronger = True
            elif r_stronger:
                to_remove.add(r)
                break
        if not is_stronger:
            reduced.difference_update(to_remove)
            reduced.add(f)
    return reduced


__all__ = [
    "canonicalize_relational_atom_vars_left",
    "canonicalize_formula_relations_vars_left",
    "extract_formula_only_initial_assumptions",
    "extract_common_formula_only_initial_assumptions",
    "merge_shared_antecedent_implications",
    "formula_only_assumptions_are_initial_or_none",
    "program_enforced_initial_formula",
    "is_safety_or_reachability_objective",
    "strip_consumed_initial_assumptions_from_objectives",
]
