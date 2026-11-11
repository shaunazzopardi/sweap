from parsing.string_to_ltl import string_to_math_expression
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct,
    disjunct_formula_set,
    is_tautology,
    propagate_nexts,
    sat,
    simplify_formula_with_math,
    strip_mathexpr,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


def _extract_numeric_constant(value: Formula) -> int | None:
    if isinstance(value, UniOp):
        if value.op == "+":
            return _extract_numeric_constant(value.right)
        if value.op == "-":
            c = _extract_numeric_constant(value.right)
            return None if c is None else -c
    if not isinstance(value, Value):
        return None
    if isinstance(value.val, BoolAtoms):
        return None
    try:
        return int(str(value.val))
    except Exception:
        return None


def _reverse_rel_op(op: str) -> str:
    return {
        "<": ">",
        "<=": ">=",
        ">": "<",
        ">=": "<=",
        "=": "=",
        "!=": "!=",
    }.get(op, op)


def _extract_next_rel_constant_for_var(
    atom: Formula, var_name: str
) -> tuple[str, int] | None:
    def _extract_from_biop(biop: BiOp) -> tuple[str, int] | None:
        op = str(biop.op)
        if op not in {"=", "!=", "<", "<=", ">", ">="}:
            return None

        left, right = biop.left, biop.right
        if (
            isinstance(left, Variable)
            and left.is_next()
            and left.prev_rep().name == var_name
        ):
            c = _extract_numeric_constant(right)
            if c is None:
                return None
            return op, c
        if (
            isinstance(right, Variable)
            and right.is_next()
            and right.prev_rep().name == var_name
        ):
            c = _extract_numeric_constant(left)
            if c is None:
                return None
            return _reverse_rel_op(op), c

        # Handle normalised forms like (-x') rel c by multiplying both sides by -1.
        if (
            isinstance(left, UniOp)
            and left.op == "-"
            and isinstance(left.right, Variable)
            and left.right.is_next()
            and left.right.prev_rep().name == var_name
        ):
            c = _extract_numeric_constant(right)
            if c is None:
                return None
            return _reverse_rel_op(op), -c
        return None

    q = strip_mathexpr(atom)
    if not isinstance(q, BiOp):
        return None
    return _extract_from_biop(q)


def _extract_next_equality_rhs_for_var(atom: Formula, var_name: str) -> Formula | None:
    q = strip_mathexpr(atom)
    if not isinstance(q, BiOp) or str(q.op) != "=":
        return None

    left = strip_mathexpr(q.left)
    right = strip_mathexpr(q.right)

    if (
        isinstance(left, Variable)
        and left.is_next()
        and left.prev_rep().name == var_name
        and not any(v for v in right.variablesin() if v.is_next())
    ):
        return strip_mathexpr(right)
    if (
        isinstance(right, Variable)
        and right.is_next()
        and right.prev_rep().name == var_name
        and not any(v for v in left.variablesin() if v.is_next())
    ):
        return strip_mathexpr(left)
    return None


def _build_formula_update_predicate_guard_replacement(
    transitions: list[Transition],
    restricted_var_to_preds: dict[str, list[Formula]],
    symbol_table,
) -> dict[Formula, Formula]:
    var_rhs_key_to_pred: dict[str, dict[str, Formula]] = {}
    pred_key_to_conds: dict[str, list[Formula]] = {}
    pred_key_to_formula: dict[str, Formula] = {}

    for var_name, preds in restricted_var_to_preds.items():
        rhs_key_to_pred: dict[str, Formula] = {}
        for pred in preds:
            rhs = _extract_next_equality_rhs_for_var(pred, var_name)
            if rhs is None:
                continue
            pred_key = str(pred)
            pred_key_to_conds.setdefault(pred_key, [])
            pred_key_to_formula[pred_key] = pred
            rhs_key_to_pred[str(strip_mathexpr(rhs))] = pred
        if len(rhs_key_to_pred) > 0:
            var_rhs_key_to_pred[var_name] = rhs_key_to_pred

    for t in transitions:
        updates_by_name = {
            str(u.left): strip_mathexpr(u.right)
            for u in t.action
            if not isinstance(u.right, NonDeterministic)
        }
        for var_name, rhs_key_to_pred in var_rhs_key_to_pred.items():
            rhs_here = updates_by_name.get(var_name)
            if rhs_here is None:
                continue
            pred = rhs_key_to_pred.get(str(rhs_here))
            if pred is None:
                continue
            pred_key_to_conds[str(pred)].append(t.condition)

    # Only replace predicate semantics by guards when the corresponding action
    # choices are mutually exclusive. For overlapping choices, keep the original
    # update predicates in the formula.
    to_replace: dict[Formula, Formula] = {}
    for var_name, preds in restricted_var_to_preds.items():
        pred_keys = [
            str(p)
            for p in preds
            if str(p) in pred_key_to_conds and len(pred_key_to_conds[str(p)]) > 0
        ]
        if len(pred_keys) == 0:
            continue

        pred_guard_disj = {
            pk: simplify_formula_with_math(
                disjunct_formula_set(pred_key_to_conds[pk]), symbol_table
            )
            for pk in pred_keys
        }

        non_exclusive = set()
        for i in range(len(pred_keys)):
            for j in range(i + 1, len(pred_keys)):
                pki = pred_keys[i]
                pkj = pred_keys[j]
                if sat(
                    conjunct(pred_guard_disj[pki], pred_guard_disj[pkj]), symbol_table
                ):
                    non_exclusive.add(pki)
                    non_exclusive.add(pkj)

        for pk in pred_keys:
            if pk in non_exclusive:
                continue
            pred = pred_key_to_formula[pk]
            replacement = pred_guard_disj[pk]
            to_replace[pred] = replacement
            if not isinstance(pred, MathExpr):
                to_replace[MathExpr(pred)] = replacement

    return to_replace


def _restricted_updates_are_pairwise_mutually_exclusive(
    restricted_var_to_preds: dict[str, list[Formula]],
    symbol_table,
) -> bool:
    for preds in restricted_var_to_preds.values():
        for i in range(len(preds)):
            for j in range(i + 1, len(preds)):
                overlap = conjunct(preds[i], preds[j])
                if sat(overlap, symbol_table):
                    return False
    return True


def _build_predicate_guard_replacement_from_partition_chain(
    restricted_var_to_preds: dict[str, list[Formula]],
    chain_update_guard_map: dict[tuple[str, str], Formula],
    symbol_table,
) -> dict[Formula, Formula]:
    to_replace: dict[Formula, Formula] = {}
    for var_name, preds in restricted_var_to_preds.items():
        for pred in preds:
            rhs = _extract_next_equality_rhs_for_var(pred, var_name)
            if rhs is None:
                continue
            key = (var_name, str(strip_mathexpr(rhs)))
            replacement = chain_update_guard_map.get(key)
            if replacement is None:
                equivalent_guards = []
                for (
                    mapped_var,
                    mapped_rhs_text,
                ), mapped_guard in chain_update_guard_map.items():
                    if mapped_var != var_name:
                        continue
                    try:
                        mapped_rhs = string_to_math_expression(mapped_rhs_text)
                    except Exception:
                        continue
                    if is_tautology(
                        BiOp(strip_mathexpr(rhs), "=", strip_mathexpr(mapped_rhs)),
                        symbol_table,
                    ):
                        equivalent_guards.append(mapped_guard)
                if len(equivalent_guards) == 0:
                    continue
                replacement = simplify_formula_with_math(
                    disjunct_formula_set(equivalent_guards), symbol_table
                )
            to_replace[pred] = replacement
            if not isinstance(pred, MathExpr):
                to_replace[MathExpr(pred)] = replacement
    return to_replace


def _rewrite_x_candidates_to_primed(
    formula: Formula, candidate_var_names: set[str]
) -> Formula:
    rel_ops = {"=", "!=", "<", "<=", ">", ">="}

    def _has_rewritable_candidate(term: Formula) -> bool:
        t = strip_mathexpr(term)
        if isinstance(t, Variable):
            return (not t.is_next()) and (t.name in candidate_var_names)
        if isinstance(t, BiOp) and str(t.op) in {"+", "-"}:
            return _has_rewritable_candidate(t.left) or _has_rewritable_candidate(
                t.right
            )
        return False

    def _prime_candidate_vars_in_term(term: Formula) -> Formula | None:
        t = strip_mathexpr(term)
        if isinstance(t, Value):
            return t
        if isinstance(t, Variable):
            if t.is_next():
                return None
            if t.name in candidate_var_names:
                return Variable(t.name + "'")
            return t
        if isinstance(t, BiOp) and str(t.op) in {"+", "-"}:
            l = _prime_candidate_vars_in_term(t.left)
            r = _prime_candidate_vars_in_term(t.right)
            if l is None or r is None:
                return None
            return BiOp(l, t.op, r)
        return None

    def _go(f: Formula):
        if isinstance(f, UniOp):
            if f.op == "X":
                right = _go(f.right)
                right_stripped = strip_mathexpr(right)
                # If the predicate already refers to any primed variable, keep
                # it unchanged under X (do not rewrite unprimed terms there).
                vars_in_right = [
                    v for v in right_stripped.variablesin() if isinstance(v, Variable)
                ]
                if any(v.is_next() for v in vars_in_right):
                    return UniOp("X", right)
                if (
                    isinstance(right_stripped, Variable)
                    and not right_stripped.is_next()
                    and right_stripped.name in candidate_var_names
                ):
                    return Variable(right_stripped.name + "'")
                if isinstance(right_stripped, Value):
                    return right_stripped
                if (
                    isinstance(right_stripped, BiOp)
                    and str(right_stripped.op) in rel_ops
                ):
                    if not (
                        _has_rewritable_candidate(right_stripped.left)
                        or _has_rewritable_candidate(right_stripped.right)
                    ):
                        return UniOp("X", right)
                    left = _prime_candidate_vars_in_term(right_stripped.left)
                    if left is not None:
                        return BiOp(left, right_stripped.op, right_stripped.right)
                    right_term = _prime_candidate_vars_in_term(right_stripped.right)
                    if right_term is not None:
                        return BiOp(right_stripped.left, right_stripped.op, right_term)
                return UniOp("X", right)
            return UniOp(f.op, _go(f.right))
        if isinstance(f, MathExpr):
            return MathExpr(_go(f.formula))
        if isinstance(f, BiOp):
            return BiOp(_go(f.left), f.op, _go(f.right))
        return f

    return _go(formula)


def _propagate_objectives_with_candidate_x_rewrite(
    objectives: list[Formula], candidate_var_names: set[str] | None = None
) -> list[Formula]:
    propagated = [propagate_nexts(f) for f in objectives]
    candidates = candidate_var_names or set()
    # Always run this pass so we still collapse X(...) around already-primed
    # variables even when there are no candidate vars to rewrite.
    return [_rewrite_x_candidates_to_primed(f, candidates) for f in propagated]


__all__ = [
    "_extract_numeric_constant",
    "_reverse_rel_op",
    "_extract_next_rel_constant_for_var",
    "_extract_next_equality_rhs_for_var",
    "_build_formula_update_predicate_guard_replacement",
    "_restricted_updates_are_pairwise_mutually_exclusive",
    "_build_predicate_guard_replacement_from_partition_chain",
    "_rewrite_x_candidates_to_primed",
    "_propagate_objectives_with_candidate_x_rewrite",
]
