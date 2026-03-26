import re
import itertools
import logging
from dataclasses import dataclass

import parsec
from parsec import choice, generate, string, sepBy, spaces, regex, many1, try_choice

import config
from analysis.smt_checker import quantifier_elimination
from parsing.util.game_transition_utils import (
    _resolve_nondeterminism,
    _complete_raw_transitions_with_lose,
)
from parsing.util.issy.reductions.ltl.spot_update_restrictions import (
    infer_spot_update_restrictions,
    prepare_restriction_scan_context,
)
from parsing.string_to_ltlmt import massage_ltl
from parsing.string_to_rpg import parity_objective
from programs.program import (
    Program,
    program_cross_product_optimized,
    fill_in_minigames,
)
from programs.transition import Transition
from programs.util import refine_init_values
from prop_lang.biop import BiOp
from prop_lang.factory import (
    create_update,
    create_var,
    create_value,
    create_mathrel,
    create_biop,
    create_neg_no,
    create_uniop,
)
from prop_lang.formula import Formula
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import (
    atomic_predicates,
    propagate_negations,
    strip_mathexpr,
    true,
    neg,
    conjunct,
    disjunct_formula_set,
    conjunct_formula_set,
    implies,
    G,
    F,
    sat,
    false,
    simplify_formula_with_math,
    is_tautology,
    extract_initial_values,
    X,
    fnode_to_formula,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from parsing.string_to_ltl import (
    string_to_math_expression,
    string_to_issy_ltl,
    unary_LTL_operators,
    binary_LTL_operators,
)
from parsing.util.issy.issy_optimisation_reporting import (
    new_optimisation_summary as _new_optimisation_summary,
    record_optimisation as _record_optimisation,
    set_last_optimisation_summary as _set_last_optimisation_summary,
)
from parsing.util.issy.reductions.ltl.formula_utils import (
    canonicalize_formula_relations_vars_left,
    extract_common_formula_only_initial_assumptions,
    extract_formula_only_initial_assumptions,
    formula_only_assumptions_are_initial_or_none as _formula_only_assumptions_are_initial_or_none,
    merge_shared_antecedent_implications,
    program_enforced_initial_formula,
    strip_consumed_initial_assumptions_from_objectives,
)
from parsing.util.issy.reductions.both.next_state_var_booleanisation import (
    _promote_next_state_vars_to_controller_props,
)
from parsing.util.game_transition_utils import (
    formula_to_transitions,
)
from parsing.util.issy.reductions.ltl.drop_unsat_initial_antecedents import (
    drop_formula_objectives_with_unsat_initial_antecedents as _drop_formula_objectives_with_unsat_initial_antecedents,
)
from parsing.util.issy.reductions.game.drop_unused_curr_input_snapshots import (
    drop_curr_input_snapshot_vars_if_no_minigames as _drop_curr_input_snapshot_vars_if_no_minigames,
)
from parsing.util.issy.reductions.ltl import (
    formula_only_paths as _formula_only_paths,
)
from pysmt.shortcuts import Exists, Not, Symbol
from pysmt.typing import BOOL, INT

name_regex = r"(?!(true|false|sys( |\()|if ))[_a-zA-Z][_a-zA-Z0-9$@\_\-]*"
name = regex(name_regex)
state = regex(r"[a-zA-Z0-9@$_-]+")

math_ops = {"=", "!=", "<", "<=", ">", ">=", "+", "-"}

unary_operators = {"not": "!", "-": "-"}
binary_operators = {"=>": "->", "=": "->", "and": "&", "or": "|"}

types = {
    "int": INTEGER,
    "bool": BOOLEAN,
    # "Real": REAL,
}

init_values = {
    INTEGER: Value("0"),
    BOOLEAN: Value(BoolAtoms.FALSE),
    # "real": Value("0.0"),
}

USE_LTL_HORIZON_INIT_VALUE_REFINEMENT = True

# Backward-compatible export for tests that patch this symbol from string_to_issy.
formula_only_assumptions_are_initial_or_none = (
    _formula_only_assumptions_are_initial_or_none
)


@dataclass(frozen=True)
class IssyProblemContext:
    inputs: list[Variable]
    state_vars: list[Variable]
    macros: dict[Variable, Formula]
    formula_objectives: list[Formula]
    symbol_table: dict[str, object]


def _record_optimisation_detail(
    summary: dict | None,
    stage: str,
    kind: str,
    detail: str,
):
    if summary is None:
        return
    details = summary.setdefault("details", [])
    details.append(
        {
            "stage": stage,
            "kind": kind,
            "detail": detail,
        }
    )


def _format_promoted_to_con_props_detail(
    promoted_by_state_var: dict[str, set[Variable]],
) -> str:
    if len(promoted_by_state_var) == 0:
        return "{}"
    parts = []
    for state_var in sorted(promoted_by_state_var.keys()):
        promoted_props = sorted(str(v) for v in promoted_by_state_var[state_var])
        parts.append(f"{state_var} -> {', '.join(promoted_props)}")
    return "{" + ", ".join(parts) + "}"


def _emit_optimisation_report(
    summary: dict | None,
    *,
    title: str,
):
    if summary is None:
        return
    details = summary.get("details", [])

    lines = [title]
    if len(details) > 0:
        for d in details:
            lines.append(f"  - {d['stage']}.{d['kind']}: {d['detail']}")
    if len(details) == 0:
        lines.append("  - no tracked optimisation/reduction details")

    report = "\n".join(lines)
    print(report)
    logging.info(report)


@generate
def issy_parser():
    vars = yield parsec.many(try_choice(macro, var_dec_parser) << spaces())
    objectives = yield parsec.many(formula_parser)

    yield spaces()
    games = yield parsec.many(issy_game_parser)
    return vars, objectives, games


@generate
def macro():
    x = yield macro_expr
    return x


@generate
def macro_val():
    yield string("def") >> spaces()
    name_str = yield name << spaces()
    yield string("=") << spaces()
    yield string("[") << spaces()
    expr = yield expr_parser
    yield string("]") << spaces()
    return name_str, expr


@generate
def macro_expr():
    yield string("def") >> spaces()
    name_str = yield name << spaces()
    yield string("=") << spaces()
    # Parse macro RHS as raw text and delegate to the ISSY LTL parser.
    # Stop when the next top-level declaration starts.
    expr_str = yield regex(r"(?s).*?(?=\n\s*(?:def|input|state|formula|game)\b|$)")
    expr_text = expr_str.strip()
    try:
        expr = string_to_issy_ltl(expr_text)
    except Exception as ltl_exc:
        # Some ISSY macros are numeric/arithmetical terms in brackets, e.g. def BOUND = [400].
        # Keep using the ISSY LTL parser by default; only fall back when needed.
        if expr_text.startswith("[") and expr_text.endswith("]"):
            expr = string_to_math_expression(expr_text[1:-1].strip())
        else:
            try:
                expr = (expr_parser << parsec.eof()).parse(expr_text)
            except Exception:
                raise ltl_exc
    return name_str, expr


@generate
def formula_parser():
    yield spaces() >> string("formula") >> spaces()
    yield string("{") << spaces()
    # parse text until "}"
    formula = yield regex(r"(?s).*?(?=})")
    yield spaces() << string("}")

    # extract assumptions and assertions
    assumptions = []
    assertions = []
    last_assumption = True
    for line in formula.splitlines():
        line = line.strip()
        if line.startswith("assume"):
            last_assumption = True
            expr = line[len("assume") :].strip()
            assumptions.append(expr)
        elif line.startswith("assert"):
            last_assumption = False
            expr = line[len("assert") :].strip()
            assertions.append(expr)
        else:
            if last_assumption:
                assumptions[-1] += " " + line
            else:
                assertions[-1] += " " + line

    assumptions_formulas = map(string_to_issy_ltl, assumptions)
    assertions_formulas = map(string_to_issy_ltl, assertions)

    return implies(
        conjunct_formula_set(assumptions_formulas),
        conjunct_formula_set(assertions_formulas),
    )


@generate
def issy_game_parser():
    yield string("game") >> spaces()
    game_type = yield name << spaces()
    yield string("from") << spaces()
    init = yield name << spaces()
    yield string("{") << spaces()
    locs = yield many1(loc_parser)
    yield spaces()
    transitions = yield many1(transition_parser)
    yield spaces()
    yield string("}") << spaces()

    return game_type, init, locs, transitions


@generate
def var_dec_parser():
    kind = yield string("input") | string("state")
    yield spaces()
    var_type = yield regex("(bool|int|real)")
    yield spaces()
    var = yield var_parser
    yield spaces()

    if var_type not in types.keys():
        raise Exception(
            str(var_type)
            + " is not a valid variable type (or real and currently unsupported)."
        )

    return var, kind, types[var_type]


@generate
def loc_parser():
    yield string("loc")
    yield spaces()
    state_name = yield name
    yield spaces()
    var_type = yield regex("[0-9]")
    yield spaces()

    return Variable(state_name), "loc", int(var_type)


@generate
def bi_expr_parser():
    first = yield expr_parser
    yield spaces()
    op = yield regex("(>=|<=|>|<|!=|=|!|\\*)")
    yield spaces()
    second = yield expr_parser

    return create_mathrel(first, op, second)


@generate
def x_expr_parser():
    yield string("(")
    yield spaces()
    op = yield regex("(\\+|-|&+|\\|+)")
    yield spaces()
    exprs = yield sepBy(expr_parser, spaces())

    if len(exprs) == 1:
        raise Exception(
            "Expression needs to have more than one argument: "
            + " ".join(map(str, exprs))
        )
    yield spaces()
    yield string(")")
    yield spaces()

    f = exprs[0]
    for e in exprs[1:]:
        f = create_biop(f, op, e)
    return f


@generate
def next_var_parser():
    v = yield name << string("'")
    return create_var(v + "'")


@generate
def var_parser():
    v = yield name
    return create_var(v)


@generate
def value_parser():
    v = yield num_value_parser | bool_value_parser
    return v


@generate
def num_value_parser():
    v = yield regex("[0-9]+")
    return create_value(int(v))


@generate
def bool_value_parser():
    v = yield choice(true_parser, false_parser)
    return v


@generate
def true_parser():
    yield string("true")
    return Value(BoolAtoms.TRUE)


@generate
def false_parser():
    yield string("false")
    return Value(BoolAtoms.FALSE)


@generate
def update_formula_parser():
    yield spaces()
    yield string("[")
    yield spaces()
    expr = yield expr_parser
    yield spaces()
    yield string("]")
    yield spaces()
    return expr


@generate
def keep_parser():
    yield spaces()
    yield string("keep")
    yield spaces()
    yield string("(")
    yield spaces()
    expr = yield many1(var_parser << spaces())
    yield spaces()
    yield string(")")
    yield spaces()
    return conjunct_formula_set([BiOp(Variable(v.name + "'"), "=", v) for v in expr])


@generate
def expr_parser():
    yield spaces()
    return (yield or_expr_parser)


@generate
def or_expr_parser():
    yield spaces()
    left = yield and_expr_parser
    yield spaces()
    rest = yield parsec.many(string("||") >> spaces() >> and_expr_parser)
    if rest:
        return disjunct_formula_set([left] + rest)
    return left


@generate
def and_expr_parser():
    yield spaces()
    left = yield comparison_expr_parser
    yield spaces()
    rest = yield parsec.many(string("&&") >> spaces() >> comparison_expr_parser)
    if rest:
        return conjunct_formula_set([left] + rest)
    return left


@generate
def comparison_expr_parser():
    yield spaces()
    yield parsec.optional(string("[")) << spaces()
    left = yield primary_expr_parser
    op = yield parsec.optional(regex("(>=|<=|>|<|!=|=)") << spaces())
    if op:
        right = yield primary_expr_parser
        result = create_mathrel(left, op, right)
    else:
        result = left
    yield spaces()
    yield parsec.optional(string("]")) << spaces()
    return result


@generate
def math_expr_parser():
    yield spaces()
    left = yield primary_math_expr_parser
    yield spaces()
    op = yield parsec.optional(regex("(\\-|\\+)") << spaces())
    if op:
        right = yield primary_math_expr_parser
        return create_mathrel(left, op, right)
    return left


@generate
def primary_math_expr_parser():
    yield spaces()
    v = yield (
        num_value_parser
        ^ next_var_parser
        ^ var_parser
        ^ (
            string("(")
            >> spaces()
            >> primary_math_expr_parser
            << spaces()
            << string(")")
        )
    )
    return v


@generate
def uni_expr_parser():
    yield spaces()
    op = yield (regex("(!|-)") << spaces())
    right = yield expr_parser
    if op == "!":
        return create_uniop(op, right)
    if op == "-":
        return create_neg_no(right)


@generate
def primary_expr_parser():
    yield spaces()
    v = (
        yield (string("(") >> spaces() >> expr_parser << spaces() << string(")"))
        ^ update_formula_parser
        ^ keep_parser
        ^ uni_expr_parser
        ^ math_expr_parser
        ^ value_parser
        ^ next_var_parser
        ^ var_parser
    )
    yield spaces()
    return v


@generate
def transition_parser():
    yield spaces()
    yield string("from")
    yield spaces()
    src = yield name
    yield spaces()
    yield string("to")
    yield spaces()
    tgt = yield name
    yield spaces()
    yield string("with")
    yield spaces()
    # gather text till you see "from " or "}"
    tran_formula_str = yield regex(r"(?s).*?(?=(\s*from\s+|\s*}))")
    if re.match(r" *keep *\((^\))+\)", tran_formula_str):
        vars = (
            tran_formula_str.replace("keep", "")
            .replace("(", "")
            .replace(")", "")
            .split(" ")
        )
        us = []
        for v in vars:
            us.append(BiOp(Variable(v + "'"), "=", Variable(v)))
        formula = conjunct_formula_set(us)
    else:
        formula = string_to_issy_ltl(tran_formula_str)
    # if any ltl ops are used, raise exception
    if (unary_LTL_operators | binary_LTL_operators).intersection(
        set(formula.ops_used())
    ):
        raise Exception(
            "LTL operators are not allowed in transition expressions: "
            + str(formula)
            + "."
        )
    yield spaces()
    return src, formula, tgt


parser = issy_parser


def string_to_issy(input: str, name_str: str) -> tuple[Program, Formula]:
    input_wo_comments = re.sub("//.*(\n|$)", "", input).strip()
    global file_name
    file_name = name_str
    vars_or_macros, objectives, games = (parser << parsec.eof()).parse(
        input_wo_comments
    )
    program, ltl_spec = process(name_str, vars_or_macros, objectives, games)

    return program, ltl_spec


def _build_process_context(vars_or_macros, formula_objectives):
    inputs = []
    state_vars = []
    macros = [v for v in vars_or_macros if len(v) == 2]

    macros = {Variable(k): v for k, v in macros}
    macros = {k: saturate_macros(v, macros) for k, v in macros.items()}

    formula_objectives = [a.replace_formulas(macros) for a in formula_objectives]
    formula_objectives = [
        strip_mathexpr(propagate_negations(f)) for f in formula_objectives
    ]
    if res := merge_shared_antecedent_implications(formula_objectives):
        formula_objectives = [res]

    vars = [v for v in vars_or_macros if len(v) == 3]
    symbol_table = {}
    for v, kind, type in vars:
        match kind:
            case "input":
                inputs.append(v)
                symbol_table[str(v)] = type
            case "state":
                state_vars.append(v)
                next_var = Variable(str(v) + "'")
                symbol_table[str(v)] = type
                symbol_table[str(next_var)] = type
            case _:
                raise Exception("Unknown var kind: " + str(kind))

    formula_objectives = [
        canonicalize_formula_relations_vars_left(f) for f in formula_objectives
    ]
    _assert_no_primed_input_references(
        formula_objectives,
        {str(v) for v in inputs},
        context="formula objectives",
    )

    return (
        inputs,
        state_vars,
        macros,
        formula_objectives,
        symbol_table,
    )


def _assert_no_primed_input_references(
    formulas: list[Formula],
    input_var_names: set[str],
    *,
    context: str,
):
    for f in formulas:
        offending = {
            str(v)
            for v in f.variablesin()
            if isinstance(v, Variable)
            and v.is_next()
            and str(v.prev_rep()) in input_var_names
        }
        if len(offending) > 0:
            raise Exception(
                "Primed input variable(s) are not allowed in ISSY "
                + context
                + ": "
                + ", ".join(offending)
                + "\nFormula: "
                + str(f)
            )


def _finalize_program_initial_values(
    program,
    formula_objectives,
    game_objectives,
    *,
    initial_state_assumptions: Formula | None = None,
):
    bad_states = (
        {"lose"} if any(str(state) == "lose" for state in program.states) else set()
    )
    refine_init_values(
        program,
        conjunct_formula_set(formula_objectives),
        use_ltl_horizon=USE_LTL_HORIZON_INIT_VALUE_REFINEMENT,
        bad_states=bad_states,
    )
    should_extract_fixed_values = (
        initial_state_assumptions is not None or len(game_objectives) == 0
    )
    if should_extract_fixed_values:
        if initial_state_assumptions is not None:
            f = initial_state_assumptions
        else:
            f = neg(conjunct_formula_set(formula_objectives))
        _, fixed_values = extract_initial_values(
            set(Variable(v) for v in program.unset_init_vars),
            f,
            program.symbol_table,
        )
        for var, val in fixed_values.items():
            program.init_var_values[str(var)] = val
            program.unset_init_vars.remove(str(var))


def _preprocess_issy_games_for_intermediate(
    games,
    macros,
    symbol_table,
    input_var_names: set[str],
):
    preprocessed_games = []
    for game_type, init, locs_in_game, transitions in games:
        preprocessed_transitions = []
        for src, f, tgt in transitions:
            ff = strip_mathexpr(
                canonicalize_formula_relations_vars_left(
                    f.replace_formulas(macros),
                )
            )
            _assert_no_primed_input_references(
                [ff],
                input_var_names,
                context=f"game transition {src} -> {tgt}",
            )
            preprocessed_transitions.append((src, ff, tgt))
        preprocessed_games.append(
            (game_type, init, locs_in_game, preprocessed_transitions)
        )
    return preprocessed_games


def _build_game_objective_and_losing_states(
    game_type: str,
    marked_states,
    program: Program,
    lose_transitions: list[Transition],
):
    losing_states = []
    states_to_exclude = set()

    match game_type:
        case "Buechi":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = G(F(objective_states))
            for scc in program.sccs:
                states_in_scc = {Variable(t.src) for t in scc}
                to_add = set()
                for s in states_in_scc:
                    to_add.update(Variable(x) for x in program.reachable_from[str(s)])
                to_add.difference_update(states_in_scc)
                states_in_scc.update(to_add)
                if len(set(marked_states[1]).intersection(states_in_scc)) == 0:
                    losing_states.extend({s.name for s in states_in_scc})
                    states_to_exclude.update(states_in_scc)
        case "Safety":
            objective = true()
            if len(marked_states[1]) != (
                len(program.states)
                if len(lose_transitions) == 0
                else len(program.states) - 1
            ):
                # if there are losing states, G(!lose) will be added
                # otherwise all states are safe, so no need to add any objective
                losing_states_here = [
                    s for s in program.states if Variable(s) not in marked_states[1]
                ]
                losing_states.extend(losing_states_here)
                states_to_exclude.update(losing_states_here)
        case "Reachability":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = F(objective_states)
            for scc in program.sccs:
                states_in_scc = {Variable(t.src) for t in scc}
                to_add = set()
                for s in states_in_scc:
                    to_add.update(Variable(x) for x in program.reachable_from[str(s)])
                to_add.difference_update(states_in_scc)
                states_in_scc.update(to_add)
                if len(set(marked_states[1]).intersection(states_in_scc)) == 0:
                    losing_states.extend({s.name for s in states_in_scc})
                    states_to_exclude.update(states_in_scc)
        case "ParityMaxOdd":
            objective = parity_objective(marked_states)
        case _:
            raise Exception("Unknown game type: " + str(game_type))

    if len(lose_transitions) > 0:
        states_to_exclude.add("lose")

    return objective, losing_states, states_to_exclude


def _build_single_intermediate_game_program(
    *,
    name_str,
    game_index: int,
    game,
    inputs,
    con_vars,
    symbol_table,
    numeric_standin_props,
    numeric_standin_to_encoding,
    optimisation_summary: dict | None = None,
):
    new_state_vars = set()
    game_type, init, locs_in_game, transitions = game

    marked_states = {}
    locs = set()
    state_to_new_state = {}
    for v, kind, type in locs_in_game:
        new_state = "game_" + str(game_index) + "_state_" + v.name
        state_to_new_state[v.name] = new_state
        locs.add(new_state)
        if type in marked_states:
            marked_states[type].append(Variable(new_state))
        else:
            marked_states[type] = [Variable(new_state)]

    init = state_to_new_state[init]
    raw_transitions = {state_to_new_state[src]: [] for src, _, _ in transitions}

    vars_in_game = {
        v if not v.is_next() else v.prev_rep()
        for _, f, _ in transitions
        for v in f.variablesin()
        if v not in inputs
    }
    vars_in_game.difference_update(con_vars)
    vars_in_game.difference_update(numeric_standin_props)

    for old_src, orig_formula, old_tgt in transitions:
        src = state_to_new_state[old_src]
        tgt = state_to_new_state[old_tgt]
        orig_formula = strip_mathexpr(orig_formula)

        cond_updates = formula_to_transitions(orig_formula, inputs, symbol_table)

        for res in cond_updates:
            if res is None:
                continue
            cond, raw_update_sets = res
            if len(numeric_standin_to_encoding) > 0:
                cond = simplify_formula_with_math(
                    cond.replace_formulas(numeric_standin_to_encoding),
                    symbol_table,
                )
            for raw_updates in raw_update_sets:
                predicate_upgrades = []
                updates = []
                for raw_update in raw_updates:
                    if len(numeric_standin_to_encoding) > 0:
                        raw_update = raw_update.replace_formulas(
                            numeric_standin_to_encoding
                        )

                    f = strip_mathexpr(raw_update)
                    if isinstance(f, Variable) and f.is_next():
                        updates.append(create_update(f.prev_rep(), true()))
                        continue
                    if (
                        isinstance(f, UniOp)
                        and f.op == "!"
                        and isinstance(f.right, Variable)
                        and f.right.is_next()
                    ):
                        updates.append(create_update(f.right.prev_rep(), false()))
                        continue

                    if isinstance(f, BiOp) and f.op == "=":
                        left, right = f.left, f.right
                        if (
                            isinstance(left, Variable)
                            and left.is_next()
                            and not any(v for v in right.variablesin() if v.is_next())
                        ):
                            updates.append(create_update(left.prev_rep(), right))
                            continue

                        if (
                            isinstance(right, Variable)
                            and right.is_next()
                            and not any(v for v in left.variablesin() if v.is_next())
                        ):
                            updates.append(create_update(right.prev_rep(), left))
                            continue

                    predicate_upgrades.append(raw_update)

                vars_updated_in_transition = {u.left for u in updates}
                vars_not_updated = vars_in_game - vars_updated_in_transition
                for v in vars_not_updated:
                    updates.append(BiOp(v, "=", NonDeterministic()))

                inputs_updates_depend_on = {
                    i
                    for u in predicate_upgrades
                    for i in u.variablesin()
                    if i in inputs
                    and len([v for v in u.variablesin() if v.is_next()]) > 1
                }
                to_replace = {}
                for inp in inputs_updates_depend_on:
                    new_var = Variable("curr_" + inp.name)
                    to_replace[inp] = new_var
                    new_state_vars.add(new_var)
                    symbol_table[str(new_var)] = symbol_table[str(inp)]
                    updates.append(Update(new_var, inp))
                predicate_upgrades = [
                    x.replace_formulas(to_replace) for x in predicate_upgrades
                ]

                t = Transition(src, cond, updates, [], tgt)
                t.set_predicate_upgrades(predicate_upgrades)
                raw_transitions[src].append(t)

    new_transitions = list(itertools.chain.from_iterable(raw_transitions.values()))
    lose_transitions = _complete_raw_transitions_with_lose(
        raw_transitions,
        symbol_table | {str(v): BOOLEAN for v in con_vars},
    )
    if len(lose_transitions) > 0:
        locs.add("lose")
    program = Program(
        name_str + "_game_" + str(game_index),
        locs,
        init,
        [(str(v), symbol_table[str(v)]) for v in vars_in_game | new_state_vars],
        new_transitions + lose_transitions,
        [(v, symbol_table[str(v)]) for v in inputs],
        [(v, BOOLEAN) for v in con_vars],
        preprocess=False,
        emit_state_binary_map=False,
    )
    logging.info(program.to_prog(""))

    marked_states = {
        i: {ss for ss in s if str(ss) in program.states}
        for i, s in marked_states.items()
    }
    objective, losing_states, states_to_exclude = (
        _build_game_objective_and_losing_states(
            game_type,
            marked_states,
            program,
            lose_transitions,
        )
    )
    collapsed_to_lose = sorted({str(s) for s in losing_states if str(s) != "lose"})
    _record_optimisation(
        optimisation_summary,
        "stage1_pre_subgames",
        "states_collapsed_to_lose",
        len(collapsed_to_lose),
    )
    if len(collapsed_to_lose) > 0:
        _record_optimisation_detail(
            optimisation_summary,
            "stage1_pre_subgames",
            "states_collapsed_to_lose",
            f"{game_type}: " + ", ".join(collapsed_to_lose),
        )
    return program, objective, losing_states, states_to_exclude


def _build_sub_programs_from_games(
    *,
    name_str,
    games,
    inputs,
    con_vars,
    symbol_table,
    numeric_standin_props,
    numeric_standin_to_encoding,
    optimisation_summary: dict | None = None,
):
    sub_programs = []
    states_to_exclude_minigame = {}
    for game_index, game in enumerate(games):
        program, objective, losing_states, states_to_exclude = (
            _build_single_intermediate_game_program(
                name_str=name_str,
                game_index=game_index,
                game=game,
                inputs=inputs,
                con_vars=con_vars,
                symbol_table=symbol_table,
                numeric_standin_props=numeric_standin_props,
                numeric_standin_to_encoding=numeric_standin_to_encoding,
                optimisation_summary=optimisation_summary,
            )
        )
        states_to_exclude_minigame[game_index] = set(states_to_exclude)
        sub_programs.append((program, objective, losing_states))
    return sub_programs, states_to_exclude_minigame


def _build_intermediate_game_program_data(
    name_str,
    games,
    problem_context: IssyProblemContext,
    optimisation_summary: dict | None = None,
):
    inputs = problem_context.inputs
    state_vars = problem_context.state_vars
    macros = problem_context.macros
    formula_objectives = problem_context.formula_objectives
    symbol_table = problem_context.symbol_table

    input_var_names = {str(v) for v in inputs}
    games = _preprocess_issy_games_for_intermediate(
        games,
        macros,
        symbol_table,
        input_var_names,
    )

    (
        formula_objectives,
        games,
        pre_promoted_new_con_props,
        numeric_promoted_by_state_var,
        numeric_standin_to_encoding,
        numeric_standin_props,
        promoted_always_primed_bool_state_vars,
    ) = _promote_next_state_vars_to_controller_props(
        games,
        formula_objectives,
        state_vars,
        symbol_table,
    )
    _record_optimisation(
        optimisation_summary,
        "stage1_pre_subgames",
        "numeric_constant_next_promoted_to_con_props",
        len(numeric_promoted_by_state_var),
    )
    if len(numeric_promoted_by_state_var) > 0:
        _record_optimisation_detail(
            optimisation_summary,
            "stage1_pre_subgames",
            "numeric_constant_next_promoted_to_con_props",
            _format_promoted_to_con_props_detail(numeric_promoted_by_state_var),
        )
    _record_optimisation(
        optimisation_summary,
        "stage1_pre_subgames",
        "always_primed_bool_promoted_controller_props",
        len(promoted_always_primed_bool_state_vars),
    )
    if len(promoted_always_primed_bool_state_vars) > 0:
        promoted_vars_txt = ", ".join(
            sorted(str(v) for v in promoted_always_primed_bool_state_vars)
        )
        _record_optimisation_detail(
            optimisation_summary,
            "stage1_pre_subgames",
            "always_primed_bool_promoted_controller_props",
            promoted_vars_txt,
        )
        logging.info(
            "Equi-realisable reduction applied: promoted always-primed boolean "
            "state var(s) to controller prop(s): %s",
            promoted_vars_txt,
        )
    if len(pre_promoted_new_con_props) > 0:
        symbol_table.update({str(v): BOOLEAN for v in pre_promoted_new_con_props})
    if len(numeric_standin_props) > 0:
        symbol_table.update({str(v): BOOLEAN for v in numeric_standin_props})

    pre_new_con_props = set(pre_promoted_new_con_props)

    con_vars = set(pre_new_con_props)
    symbol_table.update({str(v): BOOLEAN for v in pre_new_con_props})

    sub_programs, states_to_exclude_minigame = _build_sub_programs_from_games(
        name_str=name_str,
        games=games,
        inputs=inputs,
        con_vars=con_vars,
        symbol_table=symbol_table,
        numeric_standin_props=numeric_standin_props,
        numeric_standin_to_encoding=numeric_standin_to_encoding,
        optimisation_summary=optimisation_summary,
    )

    if len(numeric_standin_to_encoding) > 0:
        formula_objectives = [
            f.replace_formulas(numeric_standin_to_encoding) for f in formula_objectives
        ]
    for standin in numeric_standin_props:
        symbol_table.pop(str(standin), None)

    return (
        sub_programs,
        states_to_exclude_minigame,
        con_vars,
        symbol_table,
        list(state_vars),
        formula_objectives,
    )


def _add_missing_declared_state_vars_as_nondet_updates(
    program: Program,
    declared_state_vars: list[Variable],
    symbol_table,
) -> Program:
    if len(declared_state_vars) == 0:
        return program

    declared_state_var_names = {
        str(v) for v in declared_state_vars if str(v) in symbol_table
    }
    missing_var_names = sorted(
        name for name in declared_state_var_names if name not in program.local_vars_str
    )
    if len(missing_var_names) == 0:
        return program

    missing_vars = [Variable(name) for name in missing_var_names]
    base_transitions = (
        list(program.orig_ts)
        if hasattr(program, "orig_ts")
        else list(program.transitions)
    )

    augmented_transitions = []
    for t in base_transitions:
        new_actions = list(t.action)
        updated_vars = {str(a.left) for a in new_actions}
        for v in missing_vars:
            if str(v) not in updated_vars:
                new_actions.append(Update(v, NonDeterministic()))
        new_t = Transition(t.src, t.condition, new_actions, list(t.output), t.tgt)
        new_t.set_predicate_upgrades(list(t.pred_upgrades))
        augmented_transitions.append(new_t)

    init_values = []
    for var in program.local_vars_str + missing_var_names:
        var_type = symbol_table.get(var, program.symbol_table.get(var))
        if var_type is None:
            continue
        if var in program.init_var_values:
            init_values.append((var, var_type, program.init_var_values[var]))
        else:
            init_values.append((var, var_type))

    return Program(
        program.name,
        set(program.states),
        program.initial_state,
        init_values,
        augmented_transitions,
        list(program.env_events),
        list(program.con_events),
        preprocess=False,
        emit_state_binary_map=False,
    )


def _cross_product_intermediate_programs(
    name_str,
    sub_programs,
    states_to_exclude_minigame,
    con_vars,
    symbol_table,
    declared_state_vars,
    optimisation_summary: dict | None = None,
):
    def _is_trivial_true_objective(obj: Formula) -> bool:
        q = strip_mathexpr(obj)
        return isinstance(q, Value) and q.is_true()

    lose_var = None
    if len(sub_programs) == 1:
        program = sub_programs[0][0]
        game_objectives = (
            [sub_programs[0][1]]
            if not _is_trivial_true_objective(sub_programs[0][1])
            else []
        )
        losing_states = {0: sub_programs[0][2]}
        if len(losing_states[0]) > 0:
            lose_var = "lose"
        to_exclude_from_minigame = states_to_exclude_minigame[0]
    else:
        symbol_table.update({str(v): BOOLEAN for v in con_vars})
        losing_states = {i: sub_programs[i][2] for i in range(len(sub_programs))}
        if any(i for i, ls in losing_states.items() if len(ls) > 0):
            lose_var = "lose"

        program, prog_old_to_new_state = program_cross_product_optimized(
            [p for p, _, _ in sub_programs],
            symbol_table,
            losing_states,
            lose_var,
            name_str,
        )

        print(program.to_prog(""))
        logging.info(program.to_prog(""))
        prog_old_to_new_state = {
            i: {
                old_s: [s for s in ss if str(s) in program.states]
                for old_s, ss in prog_old_to_new_state[i].items()
            }
            for i in prog_old_to_new_state.keys()
        }
        game_objectives = [
            obj.replace(
                {
                    s: disjunct_formula_set(new_ss)
                    for s, new_ss in prog_old_to_new_state[i].items()
                }
            )
            for i, (_, obj, _) in enumerate(sub_programs)
        ]
        game_objectives = [
            obj for obj in game_objectives if not _is_trivial_true_objective(obj)
        ]
        to_exclude_from_minigame = [
            str(new_s)
            for i, ss in states_to_exclude_minigame.items()
            for s in ss
            for new_s in prog_old_to_new_state[i][Variable(s)]
        ]
        if lose_var:
            to_exclude_from_minigame.append(lose_var)

    program = _add_missing_declared_state_vars_as_nondet_updates(
        program,
        declared_state_vars,
        symbol_table,
    )
    return (
        program,
        game_objectives,
        to_exclude_from_minigame,
        lose_var,
    )


def process(
    name_str,
    vars_or_macros,
    formula_objectives,
    games,
) -> tuple[Program, Formula]:
    if len(games) == 0:
        return _process_formula_only_mode(
            name_str,
            vars_or_macros,
            formula_objectives,
        )
    return _process_games_mode(
        name_str,
        vars_or_macros,
        formula_objectives,
        games,
    )


def _process_formula_only_mode(
    name_str,
    vars_or_macros,
    formula_objectives,
) -> tuple[Program, Formula]:
    dual = config.Config.getConfig().dual
    config.Config.getConfig().dual = False
    optimisation_summary = _new_optimisation_summary(name_str)
    problem_context = _prepare_context(
        vars_or_macros=vars_or_macros,
        formula_objectives=formula_objectives,
        optimisation_summary=optimisation_summary,
    )

    (
        con_vars,
        sub_programs,
        states_to_exclude_minigame,
        symbol_table,
        declared_state_vars,
        formula_objectives,
    ) = _process_formula_only_mode_stage1(
        name_str=name_str,
        problem_context=problem_context,
        optimisation_summary=optimisation_summary,
    )
    program, new_objective = _process_pipeline_post_stage1(
        name_str=name_str,
        sub_programs=sub_programs,
        states_to_exclude_minigame=states_to_exclude_minigame,
        con_vars=con_vars,
        symbol_table=symbol_table,
        declared_state_vars=declared_state_vars,
        formula_objectives=formula_objectives,
        games=[],
        dual=dual,
        optimisation_summary=optimisation_summary,
    )
    _set_last_optimisation_summary(optimisation_summary)
    return program, new_objective


def _process_games_mode(
    name_str,
    vars_or_macros,
    formula_objectives,
    games,
) -> tuple[Program, Formula]:
    if len(games) == 0:
        raise Exception("_process_games_mode expected at least one game.")

    dual = config.Config.getConfig().dual
    config.Config.getConfig().dual = False
    optimisation_summary = _new_optimisation_summary(name_str)
    problem_context = _prepare_context(
        vars_or_macros=vars_or_macros,
        formula_objectives=formula_objectives,
        optimisation_summary=optimisation_summary,
    )

    (
        sub_programs,
        states_to_exclude_minigame,
        con_vars,
        symbol_table,
        declared_state_vars,
        formula_objectives,
    ) = _build_intermediate_game_program_data(
        name_str=name_str,
        games=games,
        problem_context=problem_context,
        optimisation_summary=optimisation_summary,
    )
    program, new_objective = _process_pipeline_post_stage1(
        name_str=name_str,
        sub_programs=sub_programs,
        states_to_exclude_minigame=states_to_exclude_minigame,
        con_vars=con_vars,
        symbol_table=symbol_table,
        declared_state_vars=declared_state_vars,
        formula_objectives=formula_objectives,
        games=games,
        dual=dual,
        optimisation_summary=optimisation_summary,
    )
    _set_last_optimisation_summary(optimisation_summary)
    return program, new_objective


def _extract_formula_only_initial_assumptions_candidate(
    formula_objectives,
    *,
    symbol_table=None,
):
    if len(formula_objectives) == 1:
        result = extract_formula_only_initial_assumptions(formula_objectives[0])
    else:
        result = extract_common_formula_only_initial_assumptions(formula_objectives)
    if result is not None:
        if not sat(result, symbol_table):
            raise Exception(
                "Assumptions are trivially UNSAT: extracted initial assumptions are unsatisfiable: "
                + str(result)
            )
        logging.info("Formula-only extracted initial assumptions: %s", result)
    return result


def _prepare_context(
    *,
    vars_or_macros,
    formula_objectives,
    optimisation_summary: dict,
) -> IssyProblemContext:
    (
        inputs,
        state_vars,
        macros,
        normalized_formula_objectives,
        symbol_table,
    ) = _build_process_context(vars_or_macros, formula_objectives)
    filtered_formula_objectives, dropped_unsat_antecedent_objectives = (
        _drop_formula_objectives_with_unsat_initial_antecedents(
            normalized_formula_objectives,
            symbol_table,
        )
    )
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "dropped_unsat_initial_antecedent_objectives",
        len(dropped_unsat_antecedent_objectives),
    )
    problem_context = IssyProblemContext(
        inputs=inputs,
        state_vars=state_vars,
        macros=dict(macros),
        formula_objectives=filtered_formula_objectives,
        symbol_table=dict(symbol_table),
    )
    return problem_context


def _qe_equivalent_update_condition(
    lhs: Formula, rhs: Formula, var_name: str, symbol_table
):
    lhs_n = strip_mathexpr(lhs)
    rhs_n = strip_mathexpr(rhs)
    if str(lhs_n) == str(rhs_n):
        return true()
    try:
        smt_ty = BOOL if symbol_table.get(var_name) == BOOLEAN else INT
        neq = neg(BiOp(lhs_n, "=", rhs_n))
        neq_smt = neq.to_smt(symbol_table)[0]
        quantified = Not(Exists([Symbol(var_name, smt_ty)], neq_smt))
        qe = quantifier_elimination(quantified)
        return simplify_formula_with_math(fnode_to_formula(qe), symbol_table)
    except Exception:
        return simplify_formula_with_math(BiOp(lhs_n, "=", rhs_n), symbol_table)


def _transitions_updates_equivalent_under_guard(
    t_left: Transition, t_right: Transition, guard: Formula, symbol_table
) -> bool:
    left_updates = {str(u.left): u.right for u in t_left.action}
    right_updates = {str(u.left): u.right for u in t_right.action}
    if set(left_updates.keys()) != set(right_updates.keys()):
        return False
    for var_name in sorted(left_updates.keys()):
        left_rhs = left_updates[var_name]
        right_rhs = right_updates[var_name]
        if isinstance(left_rhs, NonDeterministic) and isinstance(
            right_rhs, NonDeterministic
        ):
            continue
        if isinstance(left_rhs, NonDeterministic) or isinstance(
            right_rhs, NonDeterministic
        ):
            return False
        eq_cond = _qe_equivalent_update_condition(
            left_rhs,
            right_rhs,
            var_name,
            symbol_table,
        )
        if not is_tautology(implies(guard, eq_cond), symbol_table):
            return False
    return True


def _merge_extracted_transitions_with_qe_equivalent_overlaps(
    transitions: list[Transition], symbol_table
) -> tuple[list[Transition], int]:
    if len(transitions) <= 1:
        return transitions, 0
    out = []
    merged_overlap_regions = 0
    by_src = {}
    for t in transitions:
        by_src.setdefault(str(t.src), []).append(t)

    for src in sorted(by_src.keys()):
        buckets = {}
        for t in by_src[src]:
            key = (
                str(t.tgt),
                tuple(str(o) for o in t.output),
                tuple(sorted(str(p) for p in t.pred_upgrades)),
            )
            buckets.setdefault(key, []).append(t)

        for key in sorted(buckets.keys()):
            work = list(buckets[key])
            changed = True
            while changed:
                changed = False
                for i in range(len(work)):
                    if changed:
                        break
                    for j in range(i + 1, len(work)):
                        t_i = work[i]
                        t_j = work[j]
                        overlap = simplify_formula_with_math(
                            conjunct(t_i.condition, t_j.condition), symbol_table
                        )
                        if not sat(overlap, symbol_table):
                            continue
                        if not _transitions_updates_equivalent_under_guard(
                            t_i, t_j, overlap, symbol_table
                        ):
                            continue

                        left_only = simplify_formula_with_math(
                            conjunct(t_i.condition, neg(t_j.condition)),
                            symbol_table,
                        )
                        right_only = simplify_formula_with_math(
                            conjunct(t_j.condition, neg(t_i.condition)),
                            symbol_table,
                        )
                        replacement = []
                        overlap_t = Transition(
                            t_i.src,
                            overlap,
                            list(t_i.action),
                            list(t_i.output),
                            t_i.tgt,
                        )
                        overlap_t.set_predicate_upgrades(list(t_i.pred_upgrades))
                        replacement.append(overlap_t)
                        if sat(left_only, symbol_table):
                            left_t = Transition(
                                t_i.src,
                                left_only,
                                list(t_i.action),
                                list(t_i.output),
                                t_i.tgt,
                            )
                            left_t.set_predicate_upgrades(list(t_i.pred_upgrades))
                            replacement.append(left_t)
                        if sat(right_only, symbol_table):
                            right_t = Transition(
                                t_j.src,
                                right_only,
                                list(t_j.action),
                                list(t_j.output),
                                t_j.tgt,
                            )
                            right_t.set_predicate_upgrades(list(t_j.pred_upgrades))
                            replacement.append(right_t)
                        work = [
                            t for k, t in enumerate(work) if k not in {i, j}
                        ] + replacement
                        merged_overlap_regions += 1
                        changed = True
                        break
            out.extend(work)

    dedup = {}
    for t in out:
        key = (
            str(t.src),
            str(t.tgt),
            str(t.condition),
            tuple(sorted(str(a) for a in t.action)),
            tuple(sorted(str(o) for o in t.output)),
            tuple(sorted(str(p) for p in t.pred_upgrades)),
        )
        dedup[key] = t
    return [dedup[k] for k in sorted(dedup.keys())], merged_overlap_regions


def _process_formula_only_mode_stage1(
    *,
    name_str,
    problem_context: IssyProblemContext,
    optimisation_summary: dict,
):
    con_vars = set()
    sub_programs = []
    states_to_exclude_minigame = {}

    inputs = problem_context.inputs
    state_vars = problem_context.state_vars
    formula_objectives = problem_context.formula_objectives
    symbol_table = problem_context.symbol_table

    (
        formula_objectives,
        _,
        pre_promoted_new_con_props,
        numeric_promoted_by_state_var,
        numeric_standin_to_encoding,
        numeric_standin_props,
        promoted_always_primed_bool_state_vars,
    ) = _promote_next_state_vars_to_controller_props(
        [],
        formula_objectives,
        state_vars,
        symbol_table,
    )
    if len(numeric_standin_to_encoding) > 0:
        formula_objectives = [
            f.replace_formulas(numeric_standin_to_encoding) for f in formula_objectives
        ]
    for standin in numeric_standin_props:
        symbol_table.pop(str(standin), None)

    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "numeric_constant_next_promoted_to_con_props",
        len(numeric_promoted_by_state_var),
    )
    if len(numeric_promoted_by_state_var) > 0:
        _record_optimisation_detail(
            optimisation_summary,
            "formula_only",
            "numeric_constant_next_promoted_to_con_props",
            _format_promoted_to_con_props_detail(numeric_promoted_by_state_var),
        )
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "always_primed_bool_promoted_controller_props",
        len(promoted_always_primed_bool_state_vars),
    )
    if len(promoted_always_primed_bool_state_vars) > 0:
        promoted_vars_txt = ", ".join(
            sorted(str(v) for v in promoted_always_primed_bool_state_vars)
        )
        _record_optimisation_detail(
            optimisation_summary,
            "formula_only",
            "always_primed_bool_promoted_controller_props",
            promoted_vars_txt,
        )
        logging.info(
            "Equi-realisable reduction applied: promoted always-primed boolean "
            "state var(s) to controller prop(s): %s",
            promoted_vars_txt,
        )
    if len(pre_promoted_new_con_props) > 0:
        symbol_table.update({str(v): BOOLEAN for v in pre_promoted_new_con_props})

    new_con_props = pre_promoted_new_con_props

    # Keep formula-only Spot helper lookups patchable from this module (tests patch
    # string_to_issy.infer_spot_update_restrictions directly).
    _formula_only_paths.infer_spot_update_restrictions = infer_spot_update_restrictions
    _formula_only_paths.prepare_restriction_scan_context = (
        prepare_restriction_scan_context
    )

    program, formula_objectives = (
        _formula_only_paths._resolve_formula_only_fast_path_strategy(
            name_str=name_str,
            inputs=inputs,
            state_vars=state_vars,
            symbol_table=symbol_table,
            new_con_props=new_con_props,
            formula_objectives_no_snapshot=formula_objectives,
            optimisation_summary=optimisation_summary,
        )
    )
    states_to_exclude_minigame[0] = []
    declared_state_vars = list(state_vars)
    objective = true()
    losing_states = []
    sub_programs.append((program, objective, losing_states))

    return (
        con_vars,
        sub_programs,
        states_to_exclude_minigame,
        symbol_table,
        declared_state_vars,
        formula_objectives,
    )


def _process_pipeline_post_stage1(
    *,
    name_str,
    sub_programs,
    states_to_exclude_minigame,
    con_vars,
    symbol_table,
    declared_state_vars,
    formula_objectives,
    games,
    dual: bool,
    optimisation_summary: dict,
) -> tuple[Program, Formula]:
    # Stage 2: cross product of intermediate programs.
    (
        program,
        game_objectives,
        to_exclude_from_minigame,
        lose_var,
    ) = _cross_product_intermediate_programs(
        name_str,
        sub_programs,
        states_to_exclude_minigame,
        con_vars,
        symbol_table,
        declared_state_vars,
        optimisation_summary=optimisation_summary,
    )

    # Stage 3: resolve non-determinism on the combined program.
    if not program.deterministic:
        (
            program,
            post_cross_lose_var,
            to_exclude_from_minigame,
        ) = _resolve_nondeterminism(
            program,
            symbol_table,
            list(to_exclude_from_minigame),
        )
        if post_cross_lose_var:
            lose_var = post_cross_lose_var
        if not program.deterministic:
            raise Exception(
                "Program from ISSY parsing is not deterministic after post-cross-product resolution."
            )

    if dual:
        config.Config.getConfig().dual = dual

    # Stage 4: resolve minigames and finalise formula objectives.
    # we do not need to add minigames at some states:
    # if goal is safety: no need to add minigames at unsafe states
    # TODO if goal is reachability and no other games/objectives:
    #   no need to add minigames from states that cannot reach goal
    minigame_optimisation_counters = {}
    program, minigame_states = fill_in_minigames(
        program,
        formula_objectives,
        to_exclude_from_minigame,
        optimisation_counters=minigame_optimisation_counters,
    )
    # Stage-4 minigame construction counters are collected in fill_in_minigames
    # per optimised nondeterministic variable occurrence.
    _record_optimisation(
        optimisation_summary,
        "stage4_minigame",
        "constant_update_vars",
        minigame_optimisation_counters.get("minigame_constant_update_vars", 0),
    )
    _record_optimisation(
        optimisation_summary,
        "stage4_minigame",
        "not_using_int_vars",
        minigame_optimisation_counters.get("minigame_not_using_int_vars", 0),
    )
    _record_optimisation(
        optimisation_summary,
        "stage4_minigame",
        "only_inc_or_dec_vars",
        minigame_optimisation_counters.get("minigame_only_inc_or_dec_vars", 0),
    )
    if config.Config.getConfig().debug and not program.deterministic:
        raise Exception("Program is non-deterministic after minigame filling.")
    if len(games) == 0 and len(minigame_states) == 0:
        (
            program,
            formula_objectives,
            removed_curr_snapshot_vars,
        ) = _drop_curr_input_snapshot_vars_if_no_minigames(program, formula_objectives)
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "removed_curr_snapshot_vars_without_minigames",
            removed_curr_snapshot_vars,
        )

    new_formula_objectives = []
    for o in formula_objectives:
        new_o = o
        preds_in_new_o = atomic_predicates(new_o)
        to_project_into_next = {}
        for p in preds_in_new_o:
            all_next_vars = [v for v in p.variablesin() if v.is_next()]
            if len(all_next_vars) > 0:
                all_have_int_in_prog = not any(
                    v
                    for v in all_next_vars
                    if Variable("int_" + v.prev_rep().name)
                    not in program.symbol_table.keys()
                )
                if len(games) == 0 and all_have_int_in_prog:
                    # an optimisation when we know the variable is only updated by minigames
                    rename_to_int = {
                        v.prev_rep(): Variable("int_" + v.prev_rep().name)
                        for v in all_next_vars
                    }
                    to_project_into_next[p] = p.prev_rep().replace_formulas(
                        rename_to_int
                    )
                else:
                    to_project_into_next[p] = X(p.prev_rep())
        new_o = new_o.replace_formulas(to_project_into_next)
        new_formula_objectives.append(new_o)
    formula_objectives = new_formula_objectives

    if len(minigame_states) > 0:
        not_in_minigame = neg(disjunct_formula_set(minigame_states))
        formula_objectives = [
            massage_ltl(x, not_in_minigame, {}) for x in formula_objectives
        ]
        minigame_safety = G(F(neg(disjunct_formula_set(minigame_states))))
        new_game_objectives = [minigame_safety]
    else:
        new_game_objectives = []

    for game_obj in game_objectives:
        if (
            isinstance(game_obj, UniOp)
            and game_obj.op == "G"
            and not (isinstance(game_obj.right, UniOp) and game_obj.right.op == "F")
        ):
            f = game_obj.right
            f = disjunct_formula_set([f] + minigame_states)
            new_game_objectives.append(G(f))
        else:
            new_game_objectives.append(game_obj)

    effective_lose_var = (
        lose_var
        if lose_var is not None
        else ("lose" if "lose" in program.states else None)
    )
    if effective_lose_var:
        lose_safety_obj = G(neg(Variable(effective_lose_var)))
        new_game_objectives.append(lose_safety_obj)

    game_objectives = new_game_objectives

    minigame_progress_objective = None
    if len(minigame_states) > 0:
        minigame_progress_objective = G(F(neg(disjunct_formula_set(minigame_states))))

    formula_only_initial_assumptions = (
        _extract_formula_only_initial_assumptions_candidate(
            formula_objectives,
            symbol_table=program.symbol_table,
        )
    )
    can_apply_initial_extraction = (
        formula_only_initial_assumptions is not None
        and len(games) == 0
        and minigame_progress_objective is None
    )

    formula_only_init_assumptions_for_finalize = (
        formula_only_initial_assumptions if can_apply_initial_extraction else None
    )
    _finalize_program_initial_values(
        program,
        formula_objectives,
        game_objectives,
        initial_state_assumptions=formula_only_init_assumptions_for_finalize,
    )

    if can_apply_initial_extraction:
        enforced_initial_formula = program_enforced_initial_formula(program)
        (
            formula_objectives,
            removed_initial_assumption_clauses,
        ) = strip_consumed_initial_assumptions_from_objectives(
            formula_objectives,
            enforced_initial_formula,
            program.symbol_table,
        )
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "initial_assumption_implications_removed",
            removed_initial_assumption_clauses,
        )

    game_objectives_f = conjunct_formula_set(game_objectives)

    if len(formula_objectives) == 0:
        new_objective = game_objectives_f
    else:
        new_objective = conjunct_formula_set(
            [(o) for o in formula_objectives] + [game_objectives_f]
        )
    print(program.to_prog(new_objective))
    _emit_optimisation_report(
        optimisation_summary,
        title="ISSY optimisation/reduction report",
    )
    return program, new_objective


def saturate_macros(formula: Formula, macros: dict[Variable, Formula]) -> Formula:
    changed = True
    while changed:
        changed = False
        new_formula = formula.replace_formulas(macros)
        if new_formula != formula:
            changed = True
        formula = new_formula
    return formula
