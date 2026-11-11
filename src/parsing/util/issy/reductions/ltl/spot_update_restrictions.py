import spot
from dataclasses import dataclass, field
from typing import Iterable

import config
from parsing.util.issy.reductions.ltl.formula_utils import _TEMPORAL_OPS, is_canonical
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (
    atomic_predicates,
    conjunct_formula_set,
    disjunct_formula_set,
    implies,
    neg,
    propagate_nexts,
    G,
)
from prop_lang.variable import Variable

_REL_OPS = {"=", "!=", "<", "<=", ">", ">="}


@dataclass
class UpdateRestrictionResult:
    scan_context: "RestrictionScanContext"
    restricted_var_to_guard: dict[str, Formula]
    goal_scoped_restrictions: bool = False
    restricted_var_to_goal: dict[str, Formula] = field(default_factory=dict)


@dataclass(frozen=True)
class RestrictionScanContext:
    objective_for_check: Formula
    normalized_objective_for_scan: Formula
    used_relaxed_objectives: bool
    var_to_next_preds: dict[str, list[Formula]]
    allowed_next_var_names: set[str] | None


def derive_restricted_equality_update_choices(
    result: UpdateRestrictionResult,
) -> dict[str, list[Formula]] | None:
    """Return per-variable explicit RHS choices for x' = rhs predicates.

    Only variables that are already Spot-restricted are considered.
    If any restricted predicate is not a supported single-variable equality,
    return None so caller can fall back to predicate-upgrade restrictions.
    """
    debug = config.Config.getConfig().debug
    choices: dict[str, list[Formula]] = {}
    for var_name in sorted(result.restricted_var_to_guard.keys()):
        preds = result.scan_context.var_to_next_preds.get(var_name, [])
        rhs_map: dict[str, Formula] = {}
        for p in preds:
            if debug:
                if not (
                    isinstance(p, BiOp) and is_canonical(p.left, p.right, var_name)
                ):
                    raise ValueError(
                        f"Unsupported non-canonical update predicate for variable '{var_name}': {p}"
                    )
            if not isinstance(p, BiOp) or str(p.op) != "=":
                return None
            rhs = p.right
            rhs_map[str(rhs)] = rhs
        if len(rhs_map) == 0:
            return None
        choices[var_name] = [
            rhs for _, rhs in sorted(rhs_map.items(), key=lambda item: item[0])
        ]
    return choices


def _is_initial_only_formula(formula: Formula) -> bool:
    f = formula
    if any(op in _TEMPORAL_OPS for op in f.ops_used()):
        return False
    if any(v for v in f.variablesin() if isinstance(v, Variable) and v.is_next()):
        return False
    return True


def _drop_initial_only_assumption(formula: Formula) -> tuple[Formula, bool]:
    f = formula
    if not isinstance(f, BiOp) or str(f.op) != "->":
        return formula, False
    if _is_initial_only_formula(f.left):
        return f.right, True
    return formula, False


def _normalize_for_next_predicate_scan(
    formula: Formula,
    allowed_next_var_names: set[str] | None,
) -> Formula:
    from parsing.util.issy.reductions.transition_utils import (
        _rewrite_x_candidates_to_primed,
    )

    candidate_var_names = (
        set(allowed_next_var_names)
        if allowed_next_var_names is not None
        else {
            v.prev_rep().name if v.is_next() else v.name
            for v in (formula).variablesin()
            if isinstance(v, Variable)
        }
    )
    return _rewrite_x_candidates_to_primed(
        propagate_nexts(formula), candidate_var_names
    )


def _prepare_restriction_scan_objective(
    formula_objectives: list[Formula],
    *,
    allowed_next_var_names: set[str] | None,
    relax_initial_implication_assumptions: bool,
) -> tuple[Formula, bool, Formula]:
    relaxed = []
    used_relaxation = False
    for formula in formula_objectives:
        if not relax_initial_implication_assumptions:
            relaxed.append(formula)
            continue
        stripped, changed = _drop_initial_only_assumption(formula)
        relaxed.append(stripped)
        used_relaxation = used_relaxation or changed

    objective_for_check = conjunct_formula_set(relaxed)
    normalized_for_scan = _normalize_for_next_predicate_scan(
        objective_for_check, allowed_next_var_names
    )
    return objective_for_check, used_relaxation, normalized_for_scan


def prepare_restriction_scan_context(
    formula_objectives: Formula | list[Formula],
    *,
    allowed_next_var_names: set[str] | None = None,
    relax_initial_implication_assumptions: bool = True,
) -> RestrictionScanContext:
    objective_list = (
        [formula_objectives]
        if isinstance(formula_objectives, Formula)
        else formula_objectives
    )
    if len(objective_list) == 0:
        return RestrictionScanContext(
            objective_for_check=conjunct_formula_set([]),
            normalized_objective_for_scan=conjunct_formula_set([]),
            used_relaxed_objectives=False,
            var_to_next_preds={},
            allowed_next_var_names=(
                None if allowed_next_var_names is None else set(allowed_next_var_names)
            ),
        )

    objective_for_check, used_relaxation, normalized_for_scan = (
        _prepare_restriction_scan_objective(
            objective_list,
            allowed_next_var_names=allowed_next_var_names,
            relax_initial_implication_assumptions=relax_initial_implication_assumptions,
        )
    )
    var_to_next_preds = _collect_next_predicates_by_var(
        objective_for_check,
        allowed_next_var_names,
        normalized_formula=normalized_for_scan,
    )
    return RestrictionScanContext(
        objective_for_check=objective_for_check,
        normalized_objective_for_scan=normalized_for_scan,
        used_relaxed_objectives=used_relaxation,
        var_to_next_preds=var_to_next_preds,
        allowed_next_var_names=(
            None if allowed_next_var_names is None else set(allowed_next_var_names)
        ),
    )


def _collect_next_predicates_by_var(
    formula: Formula,
    allowed_next_var_names: set[str] | None,
    *,
    normalized_formula: Formula | None = None,
) -> dict[str, list[Formula]]:
    found: dict[str, dict[str, Formula]] = {}

    normalized = normalized_formula
    if normalized is None:
        normalized = _normalize_for_next_predicate_scan(formula, allowed_next_var_names)

    for q in atomic_predicates(normalized):
        if not isinstance(q, BiOp) or str(q.op) not in _REL_OPS:
            continue
        pred_next_vars = [
            v for v in q.variablesin() if isinstance(v, Variable) and v.is_next()
        ]
        pred_next_base_names = {v.prev_rep().name for v in pred_next_vars}
        if len(pred_next_base_names) != 1:
            continue
        var_name = next(iter(pred_next_base_names))
        if (
            allowed_next_var_names is not None
            and var_name not in allowed_next_var_names
        ):
            continue
        found.setdefault(var_name, {})[str(q)] = q

    return {
        var_name: [
            pred for _, pred in sorted(pred_map.items(), key=lambda item: item[0])
        ]
        for var_name, pred_map in sorted(found.items(), key=lambda item: item[0])
    }


def _collect_atom_keys(formulas: Iterable[Formula]) -> list[str]:
    atom_keys = set()
    for formula in formulas:
        for atom in atomic_predicates(formula):
            atom_keys.add(str((atom)))
    return sorted(atom_keys)


def _flatten_conjuncts(q: Formula) -> list[Formula]:
    if isinstance(q, BiOp) and q.op == "&":
        return _flatten_conjuncts(q.left) + _flatten_conjuncts(q.right)
    return [q]


def _flatten_disjuncts(q: Formula) -> list[Formula]:
    if isinstance(q, BiOp) and q.op == "|":
        return _flatten_disjuncts(q.left) + _flatten_disjuncts(q.right)
    return [q]


def _replace_atoms_with_aps(formula: Formula, atom_to_ap: dict[str, str]) -> Formula:
    def _replace(node: Formula):
        key = str((node))
        if key in atom_to_ap:
            return Variable(atom_to_ap[key])
        return None

    return formula.replace_formulas(_replace)


def spot_equivalent_to_false(formula: Formula) -> bool:
    atom_keys = _collect_atom_keys([formula])
    atom_to_ap = {atom: f"p{i}" for i, atom in enumerate(atom_keys)}
    ap_formula = _replace_atoms_with_aps(formula, atom_to_ap)

    spot_text = str(ap_formula).replace("TRUE", "true").replace("FALSE", "false")

    return spot.are_equivalent(spot.formula(spot_text), spot.formula("false"))


def infer_spot_update_restrictions(
    scan_context: RestrictionScanContext,
) -> UpdateRestrictionResult:
    objective_for_check = scan_context.objective_for_check
    var_to_next_preds = scan_context.var_to_next_preds
    if len(var_to_next_preds) == 0 and str(objective_for_check) == str(
        conjunct_formula_set([])
    ):
        return UpdateRestrictionResult(
            scan_context=scan_context,
            restricted_var_to_guard={},
        )

    restricted_var_to_guard = {}
    for var_name, preds in var_to_next_preds.items():
        if len(preds) == 0:
            continue
        disj_preds = disjunct_formula_set(preds)
        implication_check = implies(objective_for_check, neg(G(disj_preds)))
        consistency_check = conjunct_formula_set(
            [objective_for_check, neg(G(disj_preds))]
        )
        if spot_equivalent_to_false(implication_check) or spot_equivalent_to_false(
            consistency_check
        ):
            restricted_var_to_guard[var_name] = disj_preds

    return UpdateRestrictionResult(
        scan_context=scan_context,
        restricted_var_to_guard=restricted_var_to_guard,
    )


def format_spot_update_restriction_result(result: UpdateRestrictionResult) -> str:
    if len(result.scan_context.var_to_next_preds) == 0:
        return "ISSY Spot update-restriction scan: no next-state predicates found."

    lines = [
        "ISSY Spot update-restriction scan:",
        "  relaxed_initial_assumptions: "
        + str(result.scan_context.used_relaxed_objectives),
        "  goal_scoped_restrictions: " + str(result.goal_scoped_restrictions),
    ]

    for var_name in sorted(result.scan_context.var_to_next_preds.keys()):
        preds = result.scan_context.var_to_next_preds[var_name]
        restricted = var_name in result.restricted_var_to_guard
        scope_suffix = ""
        if var_name in result.restricted_var_to_goal:
            scope_suffix = ", goal=" + str(result.restricted_var_to_goal[var_name])
        lines.append(
            "  - " + var_name + " (restricted=" + str(restricted) + scope_suffix + ")"
        )
        for pred in preds:
            lines.append("      * " + str(pred))

    return "\n".join(lines)
