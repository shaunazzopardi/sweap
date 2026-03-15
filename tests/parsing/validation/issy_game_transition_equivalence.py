from __future__ import annotations

from dataclasses import dataclass
from time import perf_counter
from typing import Callable, Iterable

from pysmt.shortcuts import And, Exists, Not, get_model

from analysis.smt_checker import quantifier_elimination
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    fnode_to_formula,
    false,
    implies,
    sat,
    true, neg,
)
from prop_lang.variable import Variable


IssyGame = tuple[str, str, list[tuple[object, object, object]], list[tuple[str, Formula, str]]]


@dataclass
class SourceTransitionEquivalenceResult:
    game_index: int
    source_loc: str
    source_prog_state: str
    left_implies_right: bool
    right_implies_left: bool
    equivalent: bool


@dataclass
class GameTransitionEquivalenceResult:
    game_index: int
    equivalent: bool
    source_results: list[SourceTransitionEquivalenceResult]


@dataclass
class TransitionEquivalenceReport:
    equivalent: bool
    game_results: list[GameTransitionEquivalenceResult]


def _loc_var(game_index: int, loc: str) -> Variable:
    return Variable(f"eq_g{game_index}_loc_{loc}")


def _next_of(v: Variable) -> Variable:
    return Variable(v.name + "'")


def _loc_update_clause(loc_vars: list[Variable], tgt_loc: str) -> Formula:
    assigns = []
    for lv in loc_vars:
        is_target = lv.name.endswith(f"_{tgt_loc}")
        assigns.append(BiOp(_next_of(lv), "=", true() if is_target else false()))
    return conjunct_formula_set(assigns)


def _infer_loc_to_prog_state(
    game_index: int, locs: list[str], prog: Program
) -> tuple[dict[str, str], dict[str, str]]:
    loc_to_state: dict[str, str] = {}
    for loc in locs:
        preferred = f"game_{game_index}_state_{loc}"
        if preferred in prog.states:
            loc_to_state[loc] = preferred
            continue
        suffix_matches = [s for s in prog.states if s.endswith(f"_state_{loc}")]
        if len(suffix_matches) == 1:
            loc_to_state[loc] = suffix_matches[0]
            continue
        if loc in prog.states:
            loc_to_state[loc] = loc
            continue
        raise ValueError(
            f"Could not map ISSY loc '{loc}' in game {game_index} to a unique program state."
        )
    state_to_loc = {st: loc for loc, st in loc_to_state.items()}
    return loc_to_state, state_to_loc


def _issy_source_relation(
    game_index: int,
    source_loc: str,
    locs: list[str],
    transitions: list[tuple[str, Formula, str]],
    other_loc: str,
) -> Formula:
    loc_vars = [_loc_var(game_index, loc) for loc in locs + [other_loc]]
    clauses = []
    for src, formula, tgt in transitions:
        if src != source_loc:
            continue
        tgt_loc = tgt if tgt in set(locs) else other_loc
        clause = conjunct(formula, _loc_update_clause(loc_vars, tgt_loc))
        clauses.append(clause)
    return disjunct_formula_set(clauses) if clauses else false()


def _program_transition_relation_for_source(
    game_index: int,
    source_prog_state: str,
    prog: Program,
    state_to_loc: dict[str, str],
    locs: list[str],
    other_loc: str,
) -> Formula:
    loc_vars = [_loc_var(game_index, loc) for loc in locs + [other_loc]]
    clauses = []
    for t in prog.state_to_trans[source_prog_state]:
        if t.tgt == "lose":
            continue
        tgt_loc = state_to_loc[t.tgt] if t.tgt in state_to_loc else other_loc
        deterministic_updates = [
            BiOp(_next_of(act.left), "=", act.right)
            for act in t.action
            if not isinstance(act.right, NonDeterministic)
        ]
        clause = conjunct_formula_set(
            [t.condition]
            + deterministic_updates
            + list(t.pred_upgrades)
            + [_loc_update_clause(loc_vars, tgt_loc)]
        )
        clauses.append(clause)
    return disjunct_formula_set(clauses) if clauses else false()


def _symbol_table_with_locs(
    symbol_table: dict[str, object],
    prog_symbol_table: dict[str, object],
    game_index: int,
    locs: Iterable[str],
) -> dict[str, object]:
    out = dict(symbol_table)
    out.update(prog_symbol_table)
    for loc in locs:
        out[str(_loc_var(game_index, loc))] = BOOLEAN
    return out


def _vars_to_smt(vars_: Iterable[Variable], symbol_table: dict[str, object]):
    ordered = sorted(set(vars_), key=str)
    return [v.to_smt(symbol_table)[0] for v in ordered]


def _format_model_assignment(
    model,
    vars_of_interest: Iterable[Variable],
    symbol_table: dict[str, object],
    max_items: int = 40,
) -> str:
    lines = []
    for v in sorted(set(vars_of_interest), key=str):
        if len(lines) >= max_items:
            lines.append("... (truncated)")
            break
        try:
            sym = v.to_smt(symbol_table)[0]
            val = model.get_value(sym)
            lines.append(f"{v}={val}")
        except Exception:
            continue
    return ", ".join(lines) if lines else "<no-visible-assignment>"


def _mismatch_witnesses(
    left: Formula,
    right: Formula,
    symbol_table: dict[str, object],
    vars_of_interest: Iterable[Variable],
):
    left_smt, _ = left.to_smt(symbol_table)
    right_smt, _ = right.to_smt(symbol_table)

    m_l_not_r = get_model(And(left_smt, Not(right_smt)))
    m_r_not_l = get_model(And(right_smt, Not(left_smt)))

    witness_l_not_r = (
        _format_model_assignment(m_l_not_r, vars_of_interest, symbol_table)
        if m_l_not_r is not None
        else None
    )
    witness_r_not_l = (
        _format_model_assignment(m_r_not_l, vars_of_interest, symbol_table)
        if m_r_not_l is not None
        else None
    )
    return witness_l_not_r, witness_r_not_l


def _check_relation_equivalence(
    left: Formula,
    right: Formula,
    symbol_table: dict[str, object],
    interface_vars: set[Variable],
):
    def _project_to_interface(formula: Formula) -> Formula:
        hidden = set(formula.variablesin()).difference(interface_vars)
        if len(hidden) == 0:
            return formula
        formula_smt, _ = formula.to_smt(symbol_table)
        hidden_syms = _vars_to_smt(hidden, symbol_table)
        projected = quantifier_elimination(Exists(hidden_syms, formula_smt))
        return fnode_to_formula(projected)

    projected_left = _project_to_interface(left)
    projected_right = _project_to_interface(right)

    left_implies_right = not sat(
        conjunct(projected_left, neg(projected_right)),
        symbol_table,
    )

    right_implies_left = not sat(
        conjunct(projected_right, neg(projected_left)),
        symbol_table,
    )

    return left_implies_right, right_implies_left


def check_issy_games_vs_programs_transition_equivalence(
    issy_games: list[IssyGame],
    progs: list[Program],
    symbol_table: dict[str, object],
    input_vars: list[Variable],
    progress_cb: Callable[[str], None] | None = None,
) -> TransitionEquivalenceReport:
    if len(issy_games) != len(progs):
        raise ValueError(
            f"Expected same number of ISSY games and programs, got {len(issy_games)} and {len(progs)}."
        )

    game_results: list[GameTransitionEquivalenceResult] = []
    all_ok = True
    input_set = set(input_vars)

    def _progress(msg: str):
        if progress_cb is not None:
            progress_cb(msg)

    for game_index, (game, prog) in enumerate(zip(issy_games, progs)):
        _game_type, _init_loc, locs_in_game, transitions = game
        locs = [str(loc) for loc, _, _ in locs_in_game]
        loc_set = set(locs)
        other_loc = "__other"
        loc_to_state, state_to_loc = _infer_loc_to_prog_state(game_index, locs, prog)
        con_event_names = {str(v) for v, _ in prog.con_events}
        helper_prefixes = ("pred__", "eq_con_", "sat_con_", "game_con_")
        observable_state_vars = {
            Variable(str(v))
            for v in prog.local_vars
            if str(v) not in loc_set
            and str(v) not in con_event_names
            and not str(v).startswith(helper_prefixes)
        }
        shared_curr = set(observable_state_vars).union(input_set)
        shared_next = {_next_of(v) for v in observable_state_vars}
        shared_loc_next = {_next_of(_loc_var(game_index, loc)) for loc in locs + [other_loc]}
        interface_vars = shared_curr.union(shared_next).union(shared_loc_next)

        st = _symbol_table_with_locs(
            symbol_table, prog.symbol_table, game_index, locs + [other_loc]
        )

        source_results: list[SourceTransitionEquivalenceResult] = []
        game_ok = True
        for src in locs:
            if src not in loc_to_state:
                raise ValueError(
                    f"No program source state found for ISSY source loc '{src}' in game {game_index}."
                )
            left_rel = _issy_source_relation(game_index, src, locs, transitions, other_loc)
            right_rel = _program_transition_relation_for_source(
                game_index, loc_to_state[src], prog, state_to_loc, locs, other_loc
            )

            # If both are unsat from this source, they are equivalent for this source.
            t0 = perf_counter()
            _progress(
                f"equiv: game={game_index} src={src} stage=precheck"
            )
            if not sat(left_rel, st) and not sat(right_rel, st):
                l2r = True
                r2l = True
                _progress(
                    f"equiv: game={game_index} src={src} stage=done "
                    f"unsat_both=true elapsed={perf_counter() - t0:.3f}s"
                )
            else:
                _progress(
                    f"equiv: game={game_index} src={src} stage=implication"
                )
                l2r, r2l = _check_relation_equivalence(
                    left_rel, right_rel, st, interface_vars
                )
                _progress(
                    f"equiv: game={game_index} src={src} stage=done "
                    f"l2r={l2r} r2l={r2l} elapsed={perf_counter() - t0:.3f}s"
                )

            eq = l2r and r2l
            if not eq:
                vars_for_witness = set(left_rel.variablesin()).union(
                    set(right_rel.variablesin())
                )
                w_l_not_r, w_r_not_l = _mismatch_witnesses(
                    left_rel, right_rel, st, vars_for_witness
                )
                if not l2r and w_l_not_r is not None:
                    _progress(
                        f"equiv: game={game_index} src={src} "
                        f"witness_left_not_right: {w_l_not_r}"
                    )
                if not r2l and w_r_not_l is not None:
                    _progress(
                        f"equiv: game={game_index} src={src} "
                        f"witness_right_not_left: {w_r_not_l}"
                    )
            game_ok = game_ok and eq
            source_results.append(
                SourceTransitionEquivalenceResult(
                    game_index=game_index,
                    source_loc=src,
                    source_prog_state=loc_to_state[src],
                    left_implies_right=l2r,
                    right_implies_left=r2l,
                    equivalent=eq,
                )
            )

        all_ok = all_ok and game_ok
        game_results.append(
            GameTransitionEquivalenceResult(
                game_index=game_index,
                equivalent=game_ok,
                source_results=source_results,
            )
        )

    return TransitionEquivalenceReport(
        equivalent=all_ok,
        game_results=game_results,
    )
