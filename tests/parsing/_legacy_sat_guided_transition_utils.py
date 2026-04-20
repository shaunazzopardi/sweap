"""Legacy SAT-guided transition disjunct expansion helpers (test-only).

These are retained for benchmarking/regression comparisons against current
production transition extraction.
"""

import itertools
from multiprocessing import Pool, current_process

from pysmt.shortcuts import And, Solver

import config
from parsing.util import (
    game_transition_utils as issy_game_transition_utils_module,
)
from parsing.util.game_transition_utils import (
    _contains_next_var,
)
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    false,
    iff,
    is_tautology,
    sat,
    strip_mathexpr,
    true,
    disjunct,
    neg,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
import prop_lang.util as prop_lang_util_module


_SAT_CACHE_STATS = {
    "base_core_sat_hits": 0,
    "base_core_sat_misses": 0,
}

normalise_update = issy_game_transition_utils_module.normalise_update


def _cross_product_of_partitions(partitions):
    if len(partitions) == 0:
        return [[]]
    update_combs = []
    last_update_combs = [set()]
    for part in partitions:
        new_update_combs = []
        for u in part:
            for existing_comb in last_update_combs:
                new_comb = set(existing_comb)
                new_comb.add(u)
                new_update_combs.append(new_comb)
        last_update_combs = new_update_combs + [set()]
        update_combs.extend(new_update_combs)
    return update_combs


def _refine_partition(part, var_to_update, symbol_table):
    refined_parts = []
    updates_in_part = itertools.chain.from_iterable([var_to_update[v] for v in part])
    for u in updates_in_part:
        placed = False
        for rp in refined_parts:
            if all(not sat(conjunct(u, u2), symbol_table) for u2 in rp):
                rp.append(u)
                placed = True
                break
        if not placed:
            refined_parts.append([u])
    return refined_parts


def _partition_update_vars(var_to_update):
    update_vars = set(var_to_update.keys())
    adjacency = {v: set() for v in update_vars}
    for var, updates in var_to_update.items():
        for upd in updates:
            for dep in upd.variablesin():
                dep_name = dep.prev_rep().name if dep.is_next() else dep.name
                if dep_name in update_vars:
                    adjacency[var].add(dep_name)

    index = 0
    indices = {}
    lowlinks = {}
    stack = []
    on_stack = set()
    partitions = []

    def strongconnect(node):
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)
        for neighbor in adjacency.get(node, set()):
            if neighbor not in indices:
                strongconnect(neighbor)
                lowlinks[node] = min(lowlinks[node], lowlinks[neighbor])
            elif neighbor in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[neighbor])
        if lowlinks[node] == indices[node]:
            component = set()
            while True:
                popped = stack.pop()
                on_stack.remove(popped)
                component.add(popped)
                if popped == node:
                    break
            partitions.append(component)

    for var in sorted(update_vars):
        if var not in indices:
            strongconnect(var)
    return partitions


def handle_update_partition(updates, symbol_table):
    var_to_update = {}
    for u in updates:
        next_var = next(x for x in u.variablesin() if x.is_next())
        var_to_update.setdefault(str(next_var), set()).add(u)

    partitions = _partition_update_vars(var_to_update)
    refined_parts = []
    for part in partitions:
        refined_parts.extend(_refine_partition(part, var_to_update, symbol_table))
    return _cross_product_of_partitions(refined_parts)


def handle_update_combination(arg):
    combination, formula, _update_list, _inputs, symbol_table = arg

    if not sat(conjunct_formula_set(combination | {formula}), symbol_table):
        return None

    new_f = formula.replace_formulas(
        {u: true() for u in combination}
        | {MathExpr(u): true() for u in combination}
        | {neg(u): false() for u in combination}
        | {neg(MathExpr(u)): false() for u in combination}
    )
    if not sat(new_f, symbol_table):
        return None
    if not is_tautology(
        prop_lang_util_module.implies(
            conjunct(
                new_f,
                conjunct_formula_set(set(combination)),
            ),
            formula,
        ),
        symbol_table,
    ):
        return None
    new_f = prop_lang_util_module.simplify_formula_with_math(new_f, symbol_table)

    return new_f, frozenset(combination)


def _clone_sat_tracker(tracker):
    return {
        "pos": set(tracker["pos"]),
        "neg": set(tracker["neg"]),
        "bool_assign": dict(tracker["bool_assign"]),
        "eq": dict(tracker["eq"]),
        "neq": {k: set(v) for k, v in tracker["neq"].items()},
        "lb": dict(tracker["lb"]),
        "ub": dict(tracker["ub"]),
    }


def _new_sat_tracker():
    return {
        "pos": set(),
        "neg": set(),
        "bool_assign": {},
        "eq": {},
        "neq": {},
        "lb": {},
        "ub": {},
    }


def _negation_pair(a: Formula, b: Formula):
    return (isinstance(a, UniOp) and a.op == "!" and a.right == b) or (
        isinstance(b, UniOp) and b.op == "!" and b.right == a
    )


def _reverse_rel(op: str):
    return {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "=": "=", "!=": "!="}.get(
        op, op
    )


def _value_as_python(value: Value):
    if not isinstance(value, Value):
        return None
    if isinstance(value.val, BoolAtoms):
        return value.val == BoolAtoms.TRUE
    try:
        return int(str(value.val))
    except Exception:
        return None


def _extract_var_const_rel(atom: Formula):
    if not isinstance(atom, BiOp):
        return None
    op = str(atom.op)
    left = atom.left
    right = atom.right
    if isinstance(left, Variable) and isinstance(right, Value):
        return left, op, _value_as_python(right)
    if isinstance(right, Variable) and isinstance(left, Value):
        return right, _reverse_rel(op), _value_as_python(left)
    return None


def _extract_bool_literal(atom: Formula):
    if isinstance(atom, Variable):
        return atom.name, True
    if isinstance(atom, UniOp) and atom.op == "!" and isinstance(atom.right, Variable):
        return atom.right.name, False

    rel = _extract_var_const_rel(atom)
    if rel is None:
        return None
    var, op, val = rel
    if not isinstance(val, bool):
        return None
    if op == "=":
        return var.name, val
    if op == "!=":
        return var.name, not val
    return None


def _stronger_lb(old_lb, new_lb):
    if old_lb is None:
        return new_lb
    ov, oinc = old_lb
    nv, ninc = new_lb
    if nv > ov:
        return new_lb
    if nv < ov:
        return old_lb
    return (ov, oinc and ninc)


def _stronger_ub(old_ub, new_ub):
    if old_ub is None:
        return new_ub
    ov, oinc = old_ub
    nv, ninc = new_ub
    if nv < ov:
        return new_ub
    if nv > ov:
        return old_ub
    return (ov, oinc and ninc)


def _bounds_are_consistent(lb, ub):
    if lb is None or ub is None:
        return True
    lv, linc = lb
    uv, uinc = ub
    if lv < uv:
        return True
    if lv > uv:
        return False
    return linc and uinc


def _int_in_bounds(v: int, lb, ub):
    if lb is not None:
        lv, linc = lb
        if v < lv or (v == lv and not linc):
            return False
    if ub is not None:
        uv, uinc = ub
        if v > uv or (v == uv and not uinc):
            return False
    return True


def _cheap_add_atom(tracker, atom: Formula):
    for p in tracker["pos"]:
        if _negation_pair(p, atom):
            return False
    for n in tracker["neg"]:
        if _negation_pair(n, atom):
            return False

    if isinstance(atom, UniOp) and atom.op == "!":
        tracker["neg"].add(atom.right)
    else:
        tracker["pos"].add(atom)

    bool_lit = _extract_bool_literal(atom)
    if bool_lit is not None:
        bname, bval = bool_lit
        old_bval = tracker["bool_assign"].get(bname)
        if old_bval is not None and old_bval != bval:
            return False
        tracker["bool_assign"][bname] = bval

    rel = _extract_var_const_rel(atom)
    if rel is None:
        return True

    var, op, val = rel
    if val is None:
        return True

    key = var.name
    if isinstance(val, bool):
        old = tracker["bool_assign"].get(key)
        if op == "=":
            if old is not None and old != val:
                return False
            tracker["bool_assign"][key] = val
        elif op == "!=":
            if old is not None and old == val:
                return False
            tracker["bool_assign"][key] = not val if old is None else old
        return True

    eq = tracker["eq"].get(key)
    neqs = tracker["neq"].setdefault(key, set())
    lb = tracker["lb"].get(key)
    ub = tracker["ub"].get(key)

    if op == "=":
        if eq is not None and eq != val:
            return False
        if val in neqs:
            return False
        if not _int_in_bounds(val, lb, ub):
            return False
        tracker["eq"][key] = val
        return True

    if op == "!=":
        if eq is not None and eq == val:
            return False
        neqs.add(val)
        return True

    if op == ">":
        lb = _stronger_lb(lb, (val, False))
        tracker["lb"][key] = lb
    elif op == ">=":
        lb = _stronger_lb(lb, (val, True))
        tracker["lb"][key] = lb
    elif op == "<":
        ub = _stronger_ub(ub, (val, False))
        tracker["ub"][key] = ub
    elif op == "<=":
        ub = _stronger_ub(ub, (val, True))
        tracker["ub"][key] = ub
    else:
        return True

    if not _bounds_are_consistent(lb, ub):
        return False
    if eq is not None and not _int_in_bounds(eq, lb, ub):
        return False
    return True


def _to_smt_cached(formula, symbol_table, smt_cache):
    key = str(formula)
    cached = smt_cache.get(key)
    if cached is not None:
        return cached
    smt = And(*formula.to_smt(symbol_table))
    smt_cache[key] = smt
    return smt


def _is_boolean_branching_node(node):
    return isinstance(node, BiOp) and node.op in {"&", "|"}


def _advance_sat_guided_task(
    pending_nodes: list[Formula], current_cond: Formula, tracker, symbol_table
) -> tuple[str, object]:
    pending = list(pending_nodes)
    current = current_cond
    tr = _clone_sat_tracker(tracker)
    while pending:
        node = pending.pop()
        if isinstance(node, Value):
            if node.is_false():
                return "pruned", None
            continue

        if isinstance(node, BiOp) and node.op == "&":
            pending.extend(node.sub_formulas_up_to_associativity())
            continue

        if isinstance(node, BiOp) and node.op == "|":
            if not any(v for v in node.variablesin() if v.is_next()):
                current = conjunct(current, node)
                if not sat(current, symbol_table):
                    return "pruned", None
                continue
            branches = []
            for child in node.sub_formulas_up_to_associativity():
                child_tracker = _clone_sat_tracker(tr)
                child_feasible = None
                if not _is_boolean_branching_node(child):
                    if not _cheap_add_atom(child_tracker, child):
                        child_tracker = _clone_sat_tracker(tr)
                        child_feasible = sat(conjunct(current, child), symbol_table)
                        if not child_feasible:
                            continue

                if child_feasible is None:
                    child_feasible = sat(conjunct(current, child), symbol_table)

                if child_feasible:
                    branches.append((pending + [child], current, child_tracker))
            if len(branches) == 0:
                return "pruned", None
            return "branch", branches

        cheap_ok = _cheap_add_atom(tr, node)
        if not cheap_ok:
            if not sat(conjunct(current, node), symbol_table):
                return "pruned", None
            tr = _clone_sat_tracker(tracker)
        current = conjunct(current, node)
        if cheap_ok and not sat(current, symbol_table):
            return "pruned", None

    return "leaf", (current, tr)


def _sat_guided_collect_disjuncts_from_task(task, symbol_table) -> list[Formula]:
    pending, current, tracker = task
    leaves = []

    smt_cache = {}
    with Solver(name="msat") as solver:
        if not isinstance(current, Value) or not current.is_true():
            solver.add_assertion(_to_smt_cached(current, symbol_table, smt_cache))
            if not solver.solve():
                return leaves

        def dfs(local_pending, local_current, local_tracker):
            if len(local_pending) == 0:
                leaves.append(local_current)
                return

            node = local_pending[-1]
            rest = local_pending[:-1]

            if isinstance(node, Value):
                if node.is_false():
                    return
                dfs(rest, local_current, local_tracker)
                return

            if isinstance(node, BiOp) and node.op == "&":
                dfs(
                    rest + node.sub_formulas_up_to_associativity(),
                    local_current,
                    local_tracker,
                )
                return

            if isinstance(node, BiOp) and node.op == "|":
                if not any(v for v in node.variablesin() if v.is_next()):
                    solver.push()
                    try:
                        solver.add_assertion(
                            _to_smt_cached(node, symbol_table, smt_cache)
                        )
                        if solver.solve():
                            dfs(rest, conjunct(local_current, node), local_tracker)
                    finally:
                        solver.pop()
                    return
                for child in node.sub_formulas_up_to_associativity():
                    child_tracker = _clone_sat_tracker(local_tracker)
                    if not _is_boolean_branching_node(child):
                        if not _cheap_add_atom(child_tracker, child):
                            child_tracker = _clone_sat_tracker(local_tracker)
                            solver.push()
                            try:
                                solver.add_assertion(
                                    _to_smt_cached(child, symbol_table, smt_cache)
                                )
                                if not solver.solve():
                                    continue
                            finally:
                                solver.pop()
                    dfs(rest + [child], local_current, child_tracker)
                return

            next_tracker = _clone_sat_tracker(local_tracker)
            if not _cheap_add_atom(next_tracker, node):
                next_tracker = _clone_sat_tracker(local_tracker)
                solver.push()
                try:
                    solver.add_assertion(_to_smt_cached(node, symbol_table, smt_cache))
                    if solver.solve():
                        dfs(rest, conjunct(local_current, node), next_tracker)
                finally:
                    solver.pop()
                return

            solver.push()
            try:
                solver.add_assertion(_to_smt_cached(node, symbol_table, smt_cache))
                if solver.solve():
                    dfs(rest, conjunct(local_current, node), next_tracker)
            finally:
                solver.pop()

        dfs(pending, current, tracker)

    return leaves


def _sat_guided_disjunctive_paths(formula, symbol_table) -> list[Formula]:
    workers = max(1, config.Config.getConfig().workers)
    frontier_target = max(1, workers * 4)
    frontier = [([formula], true(), _new_sat_tracker())]
    early_leaves = []

    while frontier and len(frontier) < frontier_target:
        pending, current, tracker = frontier.pop()
        kind, data = _advance_sat_guided_task(pending, current, tracker, symbol_table)
        if kind == "leaf":
            early_leaves.append(data[0])
        elif kind == "branch":
            frontier.extend(data)

    disjuncts = list(early_leaves)
    if len(frontier) == 0:
        if config.Config.getConfig().debug and not is_tautology(
            iff(formula, disjunct_formula_set(disjuncts)), symbol_table
        ):
            raise Exception("SAT-guided expansion produced non-tautological result")

        return disjuncts

    if workers > 1 and len(frontier) > 1 and not current_process().daemon:
        with Pool(min(workers, len(frontier))) as pool:
            for chunk in pool.starmap(
                _sat_guided_collect_disjuncts_from_task,
                [(task, symbol_table) for task in frontier],
            ):
                disjuncts.extend(chunk)
    else:
        for task in frontier:
            disjuncts.extend(
                _sat_guided_collect_disjuncts_from_task(task, symbol_table)
            )

    dedup = []
    seen = set()
    for d in disjuncts:
        if d not in seen:
            dedup.append(d)
            seen.add(d)
    if config.Config.getConfig().debug and not is_tautology(
        iff(formula, disjunct_formula_set(dedup)), symbol_table
    ):
        raise Exception("SAT-guided expansion produced non-tautological result")
    return dedup


def _has_nonconjunctive_next_structure(formula: Formula) -> bool:
    q = strip_mathexpr(formula)
    if isinstance(q, BiOp):
        if q.op in {"|", "->", "<->"}:
            return any(v for v in q.variablesin() if v.is_next())
        if q.op == "&":
            return any(
                _has_nonconjunctive_next_structure(c)
                for c in q.sub_formulas_up_to_associativity()
            )
    return False


def _legacy_formula_to_transitions_compositional(formula, inputs, symbol_table):
    raw_results = _legacy_formula_to_transitions_raw_compositional(
        formula, inputs, symbol_table
    )
    return issy_game_transition_utils_module.process_cond_updates(
        raw_results, inputs, symbol_table
    )


def _formula_to_transitions_raw_base(formula, inputs, symbol_table, guard_prefix=None):
    if guard_prefix is None:
        guard_prefix = prop_lang_util_module.true()

    q = prop_lang_util_module.strip_mathexpr(formula)
    local_guard = guard_prefix
    working_formula = formula

    if isinstance(q, BiOp) and q.op == "&":
        conjuncts = q.sub_formulas_up_to_associativity()
        guarded = [c for c in conjuncts if not _contains_next_var(c)]
        update_relevant = [c for c in conjuncts if _contains_next_var(c)]
        if len(guarded) > 0 and len(update_relevant) > 0:
            local_guard = _merge_guard(
                local_guard, conjunct_formula_set(guarded), symbol_table
            )
            working_formula = conjunct_formula_set(update_relevant)
            q = prop_lang_util_module.strip_mathexpr(working_formula)

    if isinstance(q, BiOp) and q.op == "|":
        results = []
        for child in q.sub_formulas_up_to_associativity():
            results.extend(
                _formula_to_transitions_raw_base(
                    child, inputs, symbol_table, local_guard
                )
            )
        return results

    return _formula_to_transitions_raw_base_core(
        working_formula, inputs, symbol_table, local_guard
    )


def _formula_to_transitions_raw_base_core(formula, inputs, symbol_table, local_guard):
    formula = prop_lang_util_module.strip_mathexpr(formula)

    if any(v for v in formula.variablesin() if v.is_next()):
        formula_for_expansion = _expand_next_sensitive_implications(formula)
        disjuncts = _sat_guided_disjunctive_paths(formula_for_expansion, symbol_table)
        if len(disjuncts) == 0:
            return []
        if config.Config.getConfig().debug:
            disjunctive = disjunct_formula_set(disjuncts)
            if not is_tautology(iff(formula, disjunctive), symbol_table):
                raise Exception(
                    "SAT-guided disjunctive expansion is not equivalent.\n\n"
                    + str(formula)
                    + "\nvs\n"
                    + str(disjunctive)
                )
    else:
        disjuncts = [formula]

    results = []
    updates_formula_cache = {frozenset(): prop_lang_util_module.true()}
    updates_sat_cache = {}
    sat_cache: dict[str, bool] = {}

    def _sat_local(f: Formula) -> bool:
        if isinstance(f, Value):
            return f.is_true()
        key = str(f)
        cached = sat_cache.get(key)
        if cached is not None:
            _SAT_CACHE_STATS["base_core_sat_hits"] += 1
            return cached
        ok = prop_lang_util_module.sat(f, symbol_table)
        sat_cache[key] = ok
        _SAT_CACHE_STATS["base_core_sat_misses"] += 1
        return ok

    def _updates_formula(u_set: frozenset[Formula]) -> Formula:
        cached = updates_formula_cache.get(u_set)
        if cached is not None:
            return cached
        f = conjunct_formula_set(u_set)
        updates_formula_cache[u_set] = f
        return f

    def _updates_compatible(u_set: frozenset[Formula]) -> bool:
        cached = updates_sat_cache.get(u_set)
        if cached is not None:
            return cached
        ok = _sat_local(_updates_formula(u_set))
        updates_sat_cache[u_set] = ok
        return ok

    def _append_result(cond: Formula, update_preds):
        update_preds = (
            update_preds
            if isinstance(update_preds, frozenset)
            else frozenset(update_preds)
        )
        if not _updates_compatible(update_preds):
            return
        guarded_cond = _merge_guard(cond, local_guard, symbol_table)
        if _sat_local(guarded_cond):
            results.append((guarded_cond, update_preds))

    pending_disjuncts = list(disjuncts)
    while pending_disjuncts:
        d = pending_disjuncts.pop()
        if not _sat_local(d):
            continue
        updates, to_replace = extract_updates_from_formula(d)
        new_d = d.replace_formulas(to_replace)
        if config.Config.getConfig().debug:
            if not is_tautology(iff(new_d, d), symbol_table):
                raise Exception(
                    "Update extraction produced non-equivalent formula.\n\n"
                    + str(d)
                    + "\n vs \n"
                    + str(new_d)
                )
        d = new_d

        if prop_lang_util_module.is_conjunction_of_atoms(d):
            preds = d.sub_formulas_up_to_associativity() if isinstance(d, BiOp) else [d]
            update_preds = {
                p for p in preds if any(v for v in p.variablesin() if v.is_next())
            }
            cond_preds = conjunct_formula_set(p for p in preds if p not in update_preds)
            _append_result(cond_preds, frozenset(update_preds))
        else:
            # If unresolved branching is guard-only (no primed vars), do not force
            # DNF/combination expansion. We only need to disambiguate updates.
            if not _has_nonconjunctive_next_structure(d):
                updates_set = frozenset(updates)
                replacements = {}
                for u in updates_set:
                    replacements[u] = true()
                    replacements[MathExpr(u)] = true()
                    replacements[prop_lang_util_module.neg(u)] = false()
                    replacements[prop_lang_util_module.neg(MathExpr(u))] = false()
                cond_only = prop_lang_util_module.simplify_formula_with_math(
                    d.replace_formulas(replacements), symbol_table
                )
                _append_result(cond_only, updates_set)
            else:
                updates_exhaustive_eligible = len(updates) > 0 and all(
                    _is_single_next_equality_update_pred(u) for u in updates
                )
                if updates_exhaustive_eligible:
                    for combo_cond, combo_updates in generate_update_combinations(
                        d, updates, inputs, symbol_table
                    ):
                        _append_result(combo_cond, combo_updates)
                else:
                    # For non-equality update predicates, avoid power-set style
                    # update combination explosion. Split by satisfiable formula
                    # paths and let conjunction handling build the needed update sets.
                    refined = _sat_guided_disjunctive_paths(d, symbol_table)
                    refined = [r for r in refined if _sat_local(r)]
                    if len(refined) == 0:
                        continue

                    # Non-progress safety net: force a structural split only on
                    # update-bearing atoms.
                    if len(refined) == 1 and refined[0] == d:
                        atom_branches = []
                        for u in sorted(updates, key=str):
                            branch = prop_lang_util_module.simplify_formula_with_math(
                                conjunct(d, u), symbol_table
                            )
                            if branch != d and _sat_local(branch):
                                atom_branches.append(branch)
                        if len(atom_branches) > 0:
                            refined = atom_branches

                    if len(refined) == 1 and refined[0] == d:
                        # One more attempt without update-combination explosion:
                        # split by explicit top-level disjunction after DNF
                        # normalization.
                        flattened = prop_lang_util_module.only_dis_or_con_junctions(
                            prop_lang_util_module.propagate_negations(strip_mathexpr(d))
                        )
                        dnf_formula = prop_lang_util_module.almost_dnf_to_dnf(
                            flattened, 3, symbol_table
                        )
                        if isinstance(dnf_formula, BiOp) and dnf_formula.op == "|":
                            dnf_disjuncts = [
                                r
                                for r in dnf_formula.sub_formulas_up_to_associativity()
                                if _sat_local(r)
                            ]
                            if not (len(dnf_disjuncts) == 1 and dnf_disjuncts[0] == d):
                                refined = dnf_disjuncts

                    if len(refined) == 1 and refined[0] == d:
                        # Non-equality/non-single-next update formulas should not
                        # trigger exhaustive update combinations. Preserve the
                        # unresolved formula as one update predicate.
                        _append_result(prop_lang_util_module.true(), frozenset({d}))
                    else:
                        pending_disjuncts.extend(refined)
    return results


def generate_update_combinations(cond, updates, inputs, symbol_table):
    update_list = list(updates)
    if len(updates) == 0:
        return [(cond, frozenset([]))]

    update_combos = handle_update_partition(updates, symbol_table)

    print("Number of update combinations: " + str(len(update_combos)))

    with Pool(config.Config.getConfig().workers) as pool:
        rs = pool.map(
            handle_update_combination,
            [
                (combination, cond, update_list, inputs, symbol_table)
                for combination in update_combos
            ],
        )
    return rs


def extract_updates_from_formula(formula):
    preds = prop_lang_util_module.atomic_predicates(formula)
    updates = set()
    to_replace = {}
    for f in preds:
        if any(v for v in f.variablesin() if v.is_next()):
            norm_updates, norm_to_replace = normalise_update(
                prop_lang_util_module.strip_mathexpr(f)
            )
            updates.update(norm_updates)
            to_replace.update(norm_to_replace)
    return updates, to_replace


def _merge_guard(base_guard: Formula, extra_guard: Formula, symbol_table) -> Formula:
    # Let conjunct encode neutral/absorbing cases (TRUE/FALSE/etc.); then simplify.
    return prop_lang_util_module.simplify_formula_with_math(
        conjunct(base_guard, extra_guard), symbol_table
    )


def _legacy_formula_to_transitions_raw_compositional(
    formula, inputs, symbol_table, guard_prefix=None
):
    if guard_prefix is None:
        guard_prefix = issy_game_transition_utils_module.true()

    local_guard = guard_prefix

    if not isinstance(formula, issy_game_transition_utils_module.BiOp):
        return _formula_to_transitions_raw_base(
            formula, inputs, symbol_table, local_guard
        )
    if formula.op == "|":
        results = []
        for child in formula.sub_formulas_up_to_associativity():
            results.extend(
                _legacy_formula_to_transitions_raw_compositional(
                    child, inputs, symbol_table, local_guard
                )
            )
        return results
    if formula.op != "&":
        return _formula_to_transitions_raw_base(
            formula, inputs, symbol_table, local_guard
        )

    working_formula = formula
    conjuncts = working_formula.sub_formulas_up_to_associativity()
    guarded = [c for c in conjuncts if not _contains_next_var(c)]
    update_relevant = [c for c in conjuncts if _contains_next_var(c)]
    if len(guarded) > 0 and len(update_relevant) > 0:
        local_guard = _merge_guard(
            local_guard,
            issy_game_transition_utils_module.conjunct_formula_set(guarded),
            symbol_table,
        )
    if len(update_relevant) > 0:
        working_formula = issy_game_transition_utils_module.conjunct_formula_set(
            update_relevant
        )
        q = issy_game_transition_utils_module.strip_mathexpr(working_formula)
    else:
        q = issy_game_transition_utils_module.strip_mathexpr(working_formula)

    if not isinstance(q, issy_game_transition_utils_module.BiOp) or q.op != "&":
        return _formula_to_transitions_raw_base(
            working_formula, inputs, symbol_table, local_guard
        )

    conjuncts = q.sub_formulas_up_to_associativity()
    next_conjuncts = [c for c in conjuncts if _contains_next_var(c)]
    if len(next_conjuncts) <= 1:
        return _formula_to_transitions_raw_base(
            working_formula, inputs, symbol_table, local_guard
        )

    accumulated = [(issy_game_transition_utils_module.true(), frozenset())]
    for conj_formula in next_conjuncts:
        conjunct_results = _formula_to_transitions_raw_base(
            conj_formula,
            inputs,
            symbol_table,
            issy_game_transition_utils_module.true(),
        )
        if len(conjunct_results) == 0:
            return []
        next_accumulated = []
        seen = set()
        for acc_cond, acc_updates in accumulated:
            for conj_cond, conj_updates in conjunct_results:
                merged_cond = issy_game_transition_utils_module.conjunct(
                    acc_cond, conj_cond
                )
                merged_updates = acc_updates | conj_updates
                guarded_merged_cond = _merge_guard(
                    merged_cond, local_guard, symbol_table
                )
                if not issy_game_transition_utils_module.sat(
                    issy_game_transition_utils_module.conjunct_formula_set(
                        {guarded_merged_cond} | merged_updates
                    ).prev_rep(),
                    symbol_table,
                ):
                    continue
                key = (merged_cond, merged_updates)
                if key in seen:
                    continue
                seen.add(key)
                next_accumulated.append((merged_cond, merged_updates))

        if len(next_accumulated) == 0:
            return []
        accumulated = next_accumulated

    guarded_results = []
    seen_final = set()
    for cond, updates in accumulated:
        guarded_cond = _merge_guard(cond, local_guard, symbol_table)
        key = (guarded_cond, updates)
        if key in seen_final:
            continue
        seen_final.add(key)
        guarded_results.append((guarded_cond, updates))
    return guarded_results


def _legacy_formula_to_transitions_recursive_compositional(
    formula, inputs, symbol_table
):
    raw_results = _legacy_formula_to_transitions_raw_compositional_recursive(
        formula, inputs, symbol_table
    )
    return issy_game_transition_utils_module.process_cond_updates(
        raw_results, inputs, symbol_table
    )


def _legacy_formula_to_transitions_raw_compositional_recursive(
    formula, inputs, symbol_table, guard_prefix=None
):
    if guard_prefix is None:
        guard_prefix = issy_game_transition_utils_module.true()

    def _attach_guard(results, guard, check_with_updates=False):
        if len(results) == 0:
            return []
        out = []
        seen = set()
        for cond, updates in results:
            guarded_cond = _merge_guard(cond, guard, symbol_table)
            key = (guarded_cond, updates)
            if key in seen:
                continue
            sat_ok = (
                issy_game_transition_utils_module.sat(
                    issy_game_transition_utils_module.conjunct_formula_set(
                        {guarded_cond} | updates
                    ).prev_rep(),
                    symbol_table,
                )
                if check_with_updates
                else issy_game_transition_utils_module.sat(guarded_cond, symbol_table)
            )
            if sat_ok:
                seen.add(key)
                out.append((guarded_cond, updates))
        return out

    def _visit(node, inherited_guard):
        q = issy_game_transition_utils_module.strip_mathexpr(node)

        if not _contains_next_var(q):
            f = issy_game_transition_utils_module.conjunct(inherited_guard, q)
            return (
                [(f, frozenset())]
                if issy_game_transition_utils_module.sat(f, symbol_table)
                else []
            )

        if isinstance(q, issy_game_transition_utils_module.BiOp) and q.op == "|":
            out = []
            for child in q.sub_formulas_up_to_associativity():
                out.extend(_visit(child, inherited_guard))
            return out

        if isinstance(q, issy_game_transition_utils_module.BiOp) and q.op == "&":
            conjuncts = q.sub_formulas_up_to_associativity()
            guarded = [c for c in conjuncts if not _contains_next_var(c)]
            next_sensitive = [c for c in conjuncts if _contains_next_var(c)]

            local_guard = inherited_guard
            if len(guarded) > 0:
                local_guard = issy_game_transition_utils_module.conjunct(
                    local_guard,
                    issy_game_transition_utils_module.conjunct_formula_set(guarded),
                )

            if len(next_sensitive) == 1:
                child_results = _visit(
                    next_sensitive[0], issy_game_transition_utils_module.true()
                )
                return _attach_guard(
                    child_results, local_guard, check_with_updates=True
                )

            child_with_results = []
            for child in next_sensitive:
                child_results = _visit(child, issy_game_transition_utils_module.true())
                if len(child_results) == 0:
                    return []
                child_with_results.append((child, child_results))
            child_with_results.sort(key=lambda item: len(item[1]))

            accumulated = [(local_guard, frozenset())]
            for _, child_results in child_with_results:
                next_accumulated = []
                seen = set()
                for acc_cond, acc_updates in accumulated:
                    for child_cond, child_updates in child_results:
                        merged_cond = issy_game_transition_utils_module.conjunct(
                            acc_cond, child_cond
                        )
                        merged_updates = acc_updates | child_updates
                        if not issy_game_transition_utils_module.sat(
                            issy_game_transition_utils_module.conjunct_formula_set(
                                {merged_cond} | merged_updates
                            ).prev_rep(),
                            symbol_table,
                        ):
                            continue
                        key = (merged_cond, merged_updates)
                        if key in seen:
                            continue
                        seen.add(key)
                        next_accumulated.append((merged_cond, merged_updates))

                if len(next_accumulated) == 0:
                    return []
                accumulated = next_accumulated

            return accumulated

        if (
            isinstance(q, issy_game_transition_utils_module.BiOp)
            and q.op == "->"
            and _contains_next_var(q)
        ):
            expanded = _expand_next_sensitive_implications(q)
            if str(expanded) != str(q):
                return _visit(expanded, inherited_guard)

        return _formula_to_transitions_raw_base_core(
            q, inputs, symbol_table, inherited_guard
        )

    return _visit(formula, guard_prefix)


def _legacy_formula_to_transitions_iterative_compositional(
    formula, inputs, symbol_table
):
    raw_results = _legacy_formula_to_transitions_raw_compositional_iterative(
        formula, inputs, symbol_table
    )
    return issy_game_transition_utils_module.process_cond_updates(
        raw_results, inputs, symbol_table
    )


def _legacy_formula_to_transitions_raw_compositional_iterative(
    formula, inputs, symbol_table, guard_prefix=None
):
    if guard_prefix is None:
        guard_prefix = issy_game_transition_utils_module.true()

    visit_cache_true_guard = {}
    stack = [{"node": formula, "guard": guard_prefix, "state": "enter"}]
    final_result = None

    while len(stack) > 0:
        frame = stack[-1]
        state = frame["state"]

        if state == "enter":
            node = frame["node"]
            inherited_guard = frame["guard"]
            q = issy_game_transition_utils_module.strip_mathexpr(node)
            frame["q"] = q

            cache_enabled = (
                isinstance(inherited_guard, issy_game_transition_utils_module.Value)
                and inherited_guard.is_true()
            )
            cache_key = str(q) if cache_enabled else None
            frame["cache_key"] = cache_key

            if not _contains_next_var(q):
                f = issy_game_transition_utils_module.conjunct(inherited_guard, q)
                frame["result"] = (
                    [(f, frozenset())]
                    if issy_game_transition_utils_module.sat(f, symbol_table)
                    else []
                )
                frame["state"] = "return"
                continue

            if cache_key is not None:
                cached = visit_cache_true_guard.get(cache_key)
                if cached is not None:
                    frame["result"] = list(cached)
                    frame["state"] = "return"
                    continue

            if isinstance(q, issy_game_transition_utils_module.BiOp) and q.op == "|":
                frame["children"] = q.sub_formulas_up_to_associativity()
                frame["child_idx"] = 0
                frame["collected"] = []
                frame["state"] = "or_iter"
                continue

            if isinstance(q, issy_game_transition_utils_module.BiOp) and q.op == "&":
                conjuncts = q.sub_formulas_up_to_associativity()
                guarded = [c for c in conjuncts if not _contains_next_var(c)]
                next_sensitive = [c for c in conjuncts if _contains_next_var(c)]

                local_guard = inherited_guard
                if len(guarded) > 0:
                    local_guard = issy_game_transition_utils_module.conjunct(
                        local_guard,
                        issy_game_transition_utils_module.conjunct_formula_set(guarded),
                    )
                frame["local_guard"] = local_guard

                if len(next_sensitive) == 1:
                    frame["state"] = "and_single_wait"
                    stack.append(
                        {
                            "node": next_sensitive[0],
                            "guard": issy_game_transition_utils_module.true(),
                            "state": "enter",
                        }
                    )
                    continue

                frame["children"] = next_sensitive
                frame["child_idx"] = 0
                frame["child_results"] = []
                frame["state"] = "and_multi_iter"
                continue

            if (
                isinstance(q, issy_game_transition_utils_module.BiOp)
                and q.op == "->"
                and _contains_next_var(q)
            ):
                expanded = _expand_next_sensitive_implications(q)
                if str(expanded) != str(q):
                    frame["state"] = "imp_wait"
                    stack.append(
                        {
                            "node": expanded,
                            "guard": inherited_guard,
                            "state": "enter",
                        }
                    )
                    continue

            frame["result"] = _formula_to_transitions_raw_base_core(
                q, inputs, symbol_table, inherited_guard
            )
            frame["state"] = "return"
            continue

        if state == "or_iter":
            idx = frame["child_idx"]
            children = frame["children"]
            if idx >= len(children):
                frame["result"] = frame["collected"]
                frame["state"] = "return"
                continue
            frame["state"] = "or_wait"
            stack.append(
                {"node": children[idx], "guard": frame["guard"], "state": "enter"}
            )
            continue

        if state == "and_single_finalize":
            out = []
            seen = set()
            for cond, updates in frame["single_child_result"]:
                guarded_cond = issy_game_transition_utils_module.conjunct(
                    cond, frame["local_guard"]
                )
                key = (guarded_cond, updates)
                if key in seen:
                    continue
                if issy_game_transition_utils_module.sat(guarded_cond, symbol_table):
                    seen.add(key)
                    out.append((guarded_cond, updates))
            frame["result"] = out
            frame["state"] = "return"
            continue

        if state == "and_multi_iter":
            idx = frame["child_idx"]
            children = frame["children"]
            if idx >= len(children):
                child_with_results = []
                for child, child_results in zip(children, frame["child_results"]):
                    if len(child_results) == 0:
                        frame["result"] = []
                        frame["state"] = "return"
                        child_with_results = []
                        break
                    child_with_results.append((child, child_results))
                if len(child_with_results) == 0 and len(children) > 0:
                    continue

                child_with_results.sort(key=lambda item: len(item[1]))
                accumulated = [(frame["local_guard"], frozenset())]
                for _, child_results in child_with_results:
                    next_accumulated = []
                    seen = set()
                    for acc_cond, acc_updates in accumulated:
                        for child_cond, child_updates in child_results:
                            merged_cond = issy_game_transition_utils_module.conjunct(
                                acc_cond, child_cond
                            )
                            merged_updates = acc_updates | child_updates
                            if not issy_game_transition_utils_module.sat(
                                issy_game_transition_utils_module.conjunct_formula_set(
                                    {merged_cond} | merged_updates
                                ).prev_rep(),
                                symbol_table,
                            ):
                                continue
                            key = (merged_cond, merged_updates)
                            if key in seen:
                                continue
                            seen.add(key)
                            next_accumulated.append((merged_cond, merged_updates))
                    if len(next_accumulated) == 0:
                        accumulated = []
                        break
                    accumulated = next_accumulated

                frame["result"] = accumulated
                frame["state"] = "return"
                continue

            frame["state"] = "and_multi_wait"
            stack.append(
                {
                    "node": children[idx],
                    "guard": issy_game_transition_utils_module.true(),
                    "state": "enter",
                }
            )
            continue

        if state == "return":
            result_here = frame["result"]
            cache_key = frame.get("cache_key")
            if cache_key is not None:
                visit_cache_true_guard[cache_key] = tuple(result_here)

            stack.pop()
            if len(stack) == 0:
                final_result = result_here
                break

            parent = stack[-1]
            parent_state = parent["state"]
            if parent_state == "or_wait":
                parent["collected"].extend(result_here)
                parent["child_idx"] += 1
                parent["state"] = "or_iter"
                continue
            if parent_state == "and_single_wait":
                parent["single_child_result"] = result_here
                parent["state"] = "and_single_finalize"
                continue
            if parent_state == "and_multi_wait":
                parent["child_results"].append(result_here)
                parent["child_idx"] += 1
                parent["state"] = "and_multi_iter"
                continue
            if parent_state == "imp_wait":
                parent["result"] = result_here
                parent["state"] = "return"
                continue

            raise Exception(
                "Unexpected parent frame state in iterative compositional extractor: "
                + str(parent_state)
            )

        if state in {"or_wait", "and_single_wait", "and_multi_wait", "imp_wait"}:
            raise Exception(
                "Internal error: iterative extractor stalled in waiting state: "
                + str(state)
            )

        raise Exception(
            "Unknown iterative compositional extractor frame state: " + str(state)
        )

    return final_result if final_result is not None else []


def _expand_next_sensitive_implications(formula: Formula) -> Formula:
    q = strip_mathexpr(formula)
    if isinstance(q, UniOp):
        return UniOp(q.op, _expand_next_sensitive_implications(q.right))
    if not isinstance(q, BiOp):
        return q

    left = _expand_next_sensitive_implications(q.left)
    right = _expand_next_sensitive_implications(q.right)
    op = str(q.op)

    if op == "->" and (_contains_next_var(left) or _contains_next_var(right)):
        return disjunct(neg(left), right)
    if op == "<->" and (_contains_next_var(left) or _contains_next_var(right)):
        return disjunct(conjunct(left, right), conjunct(neg(left), neg(right)))

    return BiOp(left, q.op, right)


__all__ = [
    "_contains_next_var",
    "_has_nonconjunctive_next_structure",
    "_sat_guided_disjunctive_paths",
    "_legacy_formula_to_transitions_compositional",
    "_legacy_formula_to_transitions_recursive_compositional",
    "_legacy_formula_to_transitions_iterative_compositional",
]


def _is_single_next_equality_update_pred(pred: Formula) -> bool:
    q = strip_mathexpr(pred)
    if not isinstance(q, BiOp) or q.op != "=":
        return False

    left, right = q.left, q.right
    left_next = isinstance(left, Variable) and left.is_next()
    right_next = isinstance(right, Variable) and right.is_next()

    # Exactly one primed variable on one side, and no additional primed vars
    # in the opposite side expression.
    if left_next and not right_next:
        return not any(
            v for v in right.variablesin() if isinstance(v, Variable) and v.is_next()
        )
    if right_next and not left_next:
        return not any(
            v for v in left.variablesin() if isinstance(v, Variable) and v.is_next()
        )
    return False
