"""Next-state variable booleanisation reductions for ISSY games/objectives."""

from programs.util import binary_rep
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    atomic_predicates,
    false,
    propagate_nexts,
    strip_mathexpr,
    true,
)
from prop_lang.variable import Variable

from parsing.util.issy.reductions.transition_utils import (
    _extract_next_rel_constant_for_var,
    _rewrite_x_candidates_to_primed,
)
from parsing.util.issy.reductions.both.next_state_var_booleanisation_tables import (
    IssyBooleanisationTableWriter,
)


def _build_integer_regions_from_constants(
    constants: list[int],
) -> list[tuple[int | None, int | None]]:
    sorted_consts = sorted(set(constants))
    regions: list[tuple[int | None, int | None]] = []
    first = sorted_consts[0]
    regions.append((None, first - 1))
    for i, c in enumerate(sorted_consts):
        regions.append((c, c))
        if i < len(sorted_consts) - 1:
            nxt = sorted_consts[i + 1]
            if c + 1 <= nxt - 1:
                regions.append((c + 1, nxt - 1))
    last = sorted_consts[-1]
    regions.append((last + 1, None))
    return regions


def _relation_holds_on_int(value: int, op: str, c: int) -> bool:
    match op:
        case "=":
            return value == c
        case "!=":
            return value != c
        case "<":
            return value < c
        case "<=":
            return value <= c
        case ">":
            return value > c
        case ">=":
            return value >= c
        case _:
            return False


def _representative_for_region(region: tuple[int | None, int | None]) -> int:
    lb, ub = region
    if lb is None and ub is None:
        return 0
    if lb is None:
        return ub
    if ub is None:
        return lb
    return lb


def _replace_next_eq_constants_with_bool_encoding(
    formula: Formula,
    var_to_relation_encodings: dict[str, dict[tuple[str, int], Formula]],
    *,
    predicate_to_encodings: dict[str, set[str]] | None = None,
    standin_to_encoding: dict[Formula, Formula] | None = None,
) -> Formula:
    if standin_to_encoding is None:
        standin_to_encoding = {}

    def _record_encoding(raw_pred: Formula, encoded_pred: Formula):
        if predicate_to_encodings is None:
            return
        resolved = encoded_pred
        if len(standin_to_encoding) > 0:
            resolved = resolved.replace_formulas(standin_to_encoding)
        predicate_to_encodings.setdefault(str(raw_pred), set()).add(str(resolved))

    def _replace(node: Formula):
        q = strip_mathexpr(node)
        if not isinstance(q, BiOp):
            return None

        vars_here = [
            v for v in q.variablesin() if isinstance(v, Variable) and v.is_next()
        ]
        if len(vars_here) == 0:
            return None
        var_names = {v.prev_rep().name for v in vars_here}
        if len(var_names) != 1:
            return None
        var_name = next(iter(var_names))
        if var_name not in var_to_relation_encodings:
            return None

        rel = _extract_next_rel_constant_for_var(q, var_name)
        if rel is None:
            return None
        encoded = var_to_relation_encodings[var_name].get(rel)
        if encoded is None:
            return None
        _record_encoding(q, encoded)
        return encoded

    return formula.replace_formulas(_replace)


def _build_relation_driven_boolean_encoding(
    var_name: str,
    rels: set[tuple[str, int]],
    constants: set[int],
    fresh_name_fn,
) -> tuple[
    dict[tuple[str, int], Formula],
    set[Variable],
    list[tuple[str, list[tuple[int | None, int | None]], Formula]],
]:
    sorted_rels = sorted(rels, key=lambda x: (x[1], x[0]))
    base_regions = _build_integer_regions_from_constants(sorted(constants))

    signature_to_regions: dict[
        tuple[bool, ...], list[tuple[int | None, int | None]]
    ] = {}
    for region in base_regions:
        rep = _representative_for_region(region)
        sig = tuple(_relation_holds_on_int(rep, op, c) for op, c in sorted_rels)
        signature_to_regions.setdefault(sig, []).append(region)

    signature_items = list(signature_to_regions.items())
    class_labels = [
        Variable(var_name + "__class_" + str(i)) for i in range(len(signature_items))
    ]
    tmp_bin_vars, tmp_rep = binary_rep(
        class_labels,
        "tmp_" + var_name + "_",
        printing=False,
    )
    fresh_bin_vars = [Variable(fresh_name_fn(var_name)) for _ in tmp_bin_vars]
    rename = {tmp_bin_vars[i]: fresh_bin_vars[i] for i in range(len(tmp_bin_vars))}
    class_to_encoding = {
        class_labels[i]: tmp_rep[class_labels[i]].replace_formulas(rename)
        for i in range(len(class_labels))
    }

    relation_to_encoding = {}
    for rel_idx, rel in enumerate(sorted_rels):
        true_classes = []
        for class_idx, (sig, _regions) in enumerate(signature_items):
            if sig[rel_idx]:
                true_classes.append(class_labels[class_idx])
        if len(true_classes) == 0:
            relation_to_encoding[rel] = false()
        elif len(true_classes) == len(signature_items):
            relation_to_encoding[rel] = true()
        else:
            relation_to_encoding[rel] = tmp_rep.disjunct_for_keys(
                true_classes
            ).replace_formulas(rename)

    domain_rows: list[tuple[str, list[tuple[int | None, int | None]], Formula]] = []
    for class_idx, (_sig, regions) in enumerate(signature_items):
        domain_rows.append(
            (
                var_name,
                regions,
                class_to_encoding[class_labels[class_idx]],
            )
        )

    return relation_to_encoding, set(fresh_bin_vars), domain_rows


def _mentions_any_promoted_var(formula: Formula, promoted_var_names: set[str]) -> bool:
    if len(promoted_var_names) == 0:
        return False
    names_in_formula = {
        vv.prev_rep().name if vv.is_next() else vv.name for vv in formula.variablesin()
    }
    return not names_in_formula.isdisjoint(promoted_var_names)


def _identify_mixed_next_state_var_promotion_candidates(
    raw_games,
    raw_objectives,
    numeric_state_var_names: set[str],
    bool_state_var_names: set[str],
):
    candidate_rewritten_objectives = list(raw_objectives)
    numeric_final_candidates: set[str] = set()
    bool_final_candidates: set[str] = set()
    game_rels_per_var: dict[str, set[tuple[str, int]]] = {}
    constants_per_var: dict[str, set[int]] = {}
    formula_rels_per_var: dict[str, set[tuple[str, int]]] = {}
    formula_constants_per_var: dict[str, set[int]] = {}

    candidate_var_names = set(numeric_state_var_names).union(bool_state_var_names)
    if len(candidate_var_names) == 0:
        return (
            candidate_rewritten_objectives,
            numeric_final_candidates,
            bool_final_candidates,
            game_rels_per_var,
            constants_per_var,
            formula_rels_per_var,
            formula_constants_per_var,
        )

    game_formulas = [t[1] for game in raw_games for t in game[3]]
    working_var_names = set(candidate_var_names)
    invalid_vars = set()
    seen_in_games = set()

    constants_per_var = {v: set() for v in numeric_state_var_names}
    game_rels_per_var = {v: set() for v in numeric_state_var_names}

    def _invalidate_vars(var_names: set[str]) -> None:
        invalid_targets = set(var_names).intersection(working_var_names)
        if len(invalid_targets) == 0:
            return
        invalid_vars.update(invalid_targets)
        working_var_names.difference_update(invalid_targets)
        seen_in_games.difference_update(invalid_targets)
        for var_name in invalid_targets:
            constants_per_var.pop(var_name, None)
            game_rels_per_var.pop(var_name, None)

    for f in game_formulas:
        if len(working_var_names) == 0:
            break
        for atom in atomic_predicates(f):
            if len(working_var_names) == 0:
                break
            q = strip_mathexpr(atom)
            vars_here = [
                vv
                for vv in q.variablesin()
                if (vv.prev_rep().name if vv.is_next() else vv.name)
                in working_var_names
            ]
            if len(vars_here) == 0:
                continue

            if len(invalid := {vv.name for vv in vars_here if not vv.is_next()}) > 0:
                _invalidate_vars(invalid)
                continue

            base_names = {
                vv.prev_rep().name if vv.is_next() else vv.name for vv in vars_here
            }
            seen_in_games.update(base_names)
            if len(base_names) != 1:
                _invalidate_vars(
                    {v for v in base_names if v in numeric_state_var_names}
                )
                continue

            var_name = next(iter(base_names))
            if var_name not in numeric_state_var_names:
                continue
            rel = _extract_next_rel_constant_for_var(q, var_name)
            if rel is None:
                _invalidate_vars({var_name})
                continue
            rel_op, const = rel
            constants_per_var[var_name].add(const)
            game_rels_per_var[var_name].add((rel_op, const))

    if len(working_var_names) == 0:
        return (
            candidate_rewritten_objectives,
            numeric_final_candidates,
            bool_final_candidates,
            {},
            {},
            {},
            {},
        )

    propagated_objectives = [propagate_nexts(f) for f in raw_objectives]
    candidate_rewritten_objectives = list(propagated_objectives)
    broad_rewritten_objectives = [
        _rewrite_x_candidates_to_primed(f, set(working_var_names))
        for f in propagated_objectives
    ]

    objective_seen_vars = set()
    objective_rels_per_var = {v: set() for v in numeric_state_var_names}
    objective_constants_per_var = {v: set() for v in numeric_state_var_names}
    for f in broad_rewritten_objectives:
        for atom in atomic_predicates(f):
            q = strip_mathexpr(atom)
            vars_here = [
                vv
                for vv in q.variablesin()
                if (vv.prev_rep().name if vv.is_next() else vv.name)
                in working_var_names
            ]
            if len(vars_here) == 0:
                continue

            base_names = {
                vv.prev_rep().name if vv.is_next() else vv.name for vv in vars_here
            }
            objective_seen_vars.update(base_names)

            for vv in vars_here:
                if not vv.is_next():
                    invalid_vars.add(vv.name)
            if len(invalid_vars.intersection(base_names)) > 0:
                continue

            if len(base_names) != 1:
                invalid_vars.update(
                    {v for v in base_names if v in numeric_state_var_names}
                )
                continue

            var_name = next(iter(base_names))
            if var_name in invalid_vars or var_name not in numeric_state_var_names:
                continue
            rel = _extract_next_rel_constant_for_var(q, var_name)
            if rel is None:
                invalid_vars.add(var_name)
                continue
            rel_op, const = rel
            objective_rels_per_var[var_name].add((rel_op, const))
            objective_constants_per_var[var_name].add(const)

    surviving_vars = {v for v in working_var_names if v not in invalid_vars}
    if len(surviving_vars) == 0:
        return (
            candidate_rewritten_objectives,
            numeric_final_candidates,
            bool_final_candidates,
            {},
            {},
            {},
            {},
        )

    numeric_seen_in_objectives = {
        v
        for v in objective_seen_vars
        if v in numeric_state_var_names
        and v not in invalid_vars
        and len(objective_rels_per_var.get(v, set())) > 0
    }
    numeric_final_candidates = {
        v
        for v in numeric_state_var_names
        if v in surviving_vars
        and (
            (v in seen_in_games and len(constants_per_var.get(v, set())) > 0)
            or (v in numeric_seen_in_objectives)
        )
    }
    bool_final_candidates = {
        v for v in bool_state_var_names if v in surviving_vars and v not in invalid_vars
    }

    final_candidates = set(numeric_final_candidates).union(bool_final_candidates)
    if len(final_candidates) == 0:
        return (
            candidate_rewritten_objectives,
            numeric_final_candidates,
            bool_final_candidates,
            {},
            {},
            {},
            {},
        )

    formula_constants_per_var = {
        v: set(objective_constants_per_var.get(v, set()))
        for v in numeric_final_candidates
    }
    formula_rels_per_var = {
        v: set(objective_rels_per_var.get(v, set())) for v in numeric_final_candidates
    }
    candidate_rewritten_objectives = [
        (
            _rewrite_x_candidates_to_primed(f, final_candidates)
            if _mentions_any_promoted_var(f, final_candidates)
            else f
        )
        for f in propagated_objectives
    ]
    game_rels_per_var = {
        v: game_rels_per_var.get(v, set()) for v in numeric_final_candidates
    }
    constants_per_var = {
        v: constants_per_var.get(v, set()) for v in numeric_final_candidates
    }

    return (
        candidate_rewritten_objectives,
        numeric_final_candidates,
        bool_final_candidates,
        game_rels_per_var,
        constants_per_var,
        formula_rels_per_var,
        formula_constants_per_var,
    )


def _apply_con_promotion_to_bool_state_vars(
    rewritten_games_in,
    rewritten_objectives_in,
    promoted_var_names: set[str],
    curr_state_vars,
    symbol_table,
    existing_con_props: set[Variable],
):
    if len(promoted_var_names) == 0:
        return rewritten_games_in, rewritten_objectives_in, set(), set()

    promoted_bool_state_vars = {
        v for v in curr_state_vars if str(v) in promoted_var_names
    }
    if len(promoted_bool_state_vars) == 0:
        return rewritten_games_in, rewritten_objectives_in, set(), set()

    promoted_names = {str(v) for v in promoted_bool_state_vars}
    used_names = set(symbol_table.keys()).difference(promoted_names).difference(
        {name + "'" for name in promoted_names}
    ) | {str(v) for v in existing_con_props}
    promoted_bool_state_to_con_prop = {}
    for v in sorted(promoted_bool_state_vars, key=str):
        base_name = str(v)
        candidate = base_name
        suffix = 1
        while candidate in used_names:
            candidate = f"primed_{base_name}_{suffix}"
            suffix += 1
        used_names.add(candidate)
        promoted_bool_state_to_con_prop[v] = Variable(candidate)

    next_to_promoted_bit = {
        Variable(str(v) + "'"): promoted_bool_state_to_con_prop[v]
        for v in promoted_bool_state_vars
    }
    rewritten_objectives = [
        f.replace_formulas(next_to_promoted_bit) for f in rewritten_objectives_in
    ]
    rewritten_games = []
    for game_type, init, locs_in_game, transitions in rewritten_games_in:
        rewritten_transitions = []
        for src, f, tgt in transitions:
            rewritten_transitions.append(
                (src, f.replace_formulas(next_to_promoted_bit), tgt)
            )
        rewritten_games.append((game_type, init, locs_in_game, rewritten_transitions))
    curr_state_vars[:] = [
        v for v in curr_state_vars if v not in promoted_bool_state_vars
    ]
    return (
        rewritten_games,
        rewritten_objectives,
        set(promoted_bool_state_to_con_prop.values()),
        promoted_bool_state_vars,
    )


def _promote_next_state_vars_to_controller_props(
    raw_games,
    raw_objectives,
    curr_state_vars,
    symbol_table,
):
    numeric_state_var_names = {
        str(v) for v in curr_state_vars if symbol_table.get(str(v)) != BOOLEAN
    }
    bool_state_var_names = {
        str(v) for v in curr_state_vars if symbol_table.get(str(v)) == BOOLEAN
    }
    if len(numeric_state_var_names) == 0 and len(bool_state_var_names) == 0:
        return raw_objectives, raw_games, set(), {}, {}, set(), set()

    (
        candidate_rewritten_objectives,
        numeric_candidates,
        bool_candidates,
        game_rels_per_var,
        constants_per_var,
        formula_rels_per_var,
        formula_constants_per_var,
    ) = _identify_mixed_next_state_var_promotion_candidates(
        raw_games,
        raw_objectives,
        numeric_state_var_names,
        bool_state_var_names,
    )
    if len(numeric_candidates) == 0 and len(bool_candidates) == 0:
        return raw_objectives, raw_games, set(), {}, {}, set(), set()

    rewritten_objectives = list(candidate_rewritten_objectives)
    rewritten_games = raw_games
    promoted_con_props = set()
    numeric_var_to_promoted_props = {}
    standin_to_encoding = {}
    standin_props = set()

    if len(numeric_candidates) > 0:
        (
            rewritten_objectives,
            rewritten_games,
            numeric_promoted_con_props,
            numeric_var_to_promoted_props,
            standin_to_encoding,
            standin_props,
        ) = _apply_con_promotion_to_numeric_state_vars(
            raw_games,
            rewritten_objectives,
            numeric_candidates,
            game_rels_per_var,
            constants_per_var,
            formula_rels_per_var,
            formula_constants_per_var,
            curr_state_vars,
            symbol_table,
        )
        promoted_con_props.update(numeric_promoted_con_props)

    if len(bool_candidates) > 0:
        (
            rewritten_games,
            rewritten_objectives,
            bool_promoted_con_props,
            promoted_bool_state_vars,
        ) = _apply_con_promotion_to_bool_state_vars(
            rewritten_games,
            rewritten_objectives,
            bool_candidates,
            curr_state_vars,
            symbol_table,
            promoted_con_props,
        )
        promoted_con_props.update(bool_promoted_con_props)
    else:
        promoted_bool_state_vars = set()

    return (
        rewritten_objectives,
        rewritten_games,
        promoted_con_props,
        numeric_var_to_promoted_props,
        standin_to_encoding,
        standin_props,
        promoted_bool_state_vars,
    )


def _apply_con_promotion_to_numeric_state_vars(
    raw_games,
    rewritten_objectives_in,
    final_candidates: set[str],
    game_rels_per_var: dict[str, set[tuple[str, int]]],
    constants_per_var: dict[str, set[int]],
    formula_rels_per_var: dict[str, set[tuple[str, int]]],
    formula_constants_per_var: dict[str, set[int]],
    curr_state_vars,
    symbol_table,
):
    used_names = set(symbol_table.keys())
    var_to_relation_encodings: dict[str, dict[tuple[str, int], Formula]] = {}
    domain_rows: list[tuple[str, list[tuple[int | None, int | None]], Formula]] = []
    promoted_con_props = set()
    promoted_props_by_var: dict[str, set[Variable]] = {}
    standin_to_encoding: dict[Formula, Formula] = {}
    standin_props = set()
    predicate_to_encodings: dict[str, set[str]] = {}

    def _fresh_var_name(base: str):
        i = 1
        candidate = f"{base}{i}"
        while candidate in used_names:
            i += 1
            candidate = f"{base}{i}"
        used_names.add(candidate)
        return candidate

    for var_name in sorted(final_candidates):
        rels = set(game_rels_per_var.get(var_name, set())).union(
            formula_rels_per_var.get(var_name, set())
        )
        constants = set(constants_per_var.get(var_name, set())).union(
            formula_constants_per_var.get(var_name, set())
        )
        constants.update(c for _, c in rels)
        if len(rels) == 0 or len(constants) == 0:
            continue

        relation_to_encoding, fresh_bin_vars, var_domain_rows = (
            _build_relation_driven_boolean_encoding(
                var_name,
                rels,
                constants,
                _fresh_var_name,
            )
        )

        promoted_con_props.update(fresh_bin_vars)
        promoted_props_by_var[var_name] = set(fresh_bin_vars)
        domain_rows.extend(var_domain_rows)

        relation_refs = {}
        for rel, encoding in relation_to_encoding.items():
            standin = Variable(_fresh_var_name(var_name + "__pred_standin_"))
            relation_refs[rel] = standin
            standin_to_encoding[standin] = encoding
            standin_props.add(standin)
        var_to_relation_encodings[var_name] = relation_refs

    if len(var_to_relation_encodings) == 0:
        return rewritten_objectives_in, raw_games, set(), {}, {}, set()

    promoted_var_names = set(var_to_relation_encodings.keys())

    rewritten_games = []
    for game_type, init, locs_in_game, transitions in raw_games:
        rewritten_transitions = []
        for src, f, tgt in transitions:
            if _mentions_any_promoted_var(f, promoted_var_names):
                rewritten_f = _replace_next_eq_constants_with_bool_encoding(
                    f,
                    var_to_relation_encodings,
                    predicate_to_encodings=predicate_to_encodings,
                    standin_to_encoding=standin_to_encoding,
                )
            else:
                rewritten_f = f
            rewritten_transitions.append((src, rewritten_f, tgt))
        rewritten_games.append((game_type, init, locs_in_game, rewritten_transitions))

    rewritten_objectives = []
    for f in rewritten_objectives_in:
        if _mentions_any_promoted_var(f, promoted_var_names):
            rewritten_objectives.append(
                _replace_next_eq_constants_with_bool_encoding(
                    f,
                    var_to_relation_encodings,
                    predicate_to_encodings=predicate_to_encodings,
                    standin_to_encoding=standin_to_encoding,
                )
            )
        else:
            rewritten_objectives.append(f)
    IssyBooleanisationTableWriter.emit_numeric_boolean_domain_mapping(
        domain_rows, standin_to_encoding
    )
    IssyBooleanisationTableWriter.emit_numeric_predicate_boolean_mapping(
        predicate_to_encodings
    )

    converted_vars = {Variable(v) for v in promoted_var_names}
    curr_state_vars[:] = [v for v in curr_state_vars if v not in converted_vars]
    for var_name in promoted_var_names:
        symbol_table.pop(var_name, None)
        symbol_table.pop(var_name + "'", None)

    return (
        rewritten_objectives,
        rewritten_games,
        promoted_con_props,
        promoted_props_by_var,
        standin_to_encoding,
        standin_props,
    )
