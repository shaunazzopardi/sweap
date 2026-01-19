import re
import itertools
from multiprocessing import Pool
from typing import List, Optional

import parsec
from parsec import choice, generate, string, sepBy, spaces, regex, many1, try_choice
from pysmt.logics import BOOL
from pysmt.shortcuts import Exists, And, Symbol
from pysmt.typing import INT

from analysis.smt_checker import bdd_simplify, quantifier_elimination
import config
from parsing.string_to_ltlmt import massage_ltl, partition_updates, update_combinations
from parsing.string_to_rpg import parity_objective
from programs.program import Program, program_cross_product, fill_in_minigames
from programs.transition import Transition
from programs.util import binary_rep, powerset, refine_init_values
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
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.util import (
    atomic_predicates,
    fnode_to_formula,
    is_conjunction_of_atoms,
    is_tautology,
    only_dis_or_con_junctions,
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
    disjunct,
    sat,
    dnf,
    false,
    simplify_formula_with_math,
    extract_initial_values,
    is_dnf,
    is_contradictory,
    normalize_ltl,
    X,
    stringify_pred,
    almost_dnf_to_dnf,
    iff,
    cancel_double_negations,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from parsing.string_to_ltl import (
    fnode_to_issy_formula,
    string_to_issy_ltl,
    unary_LTL_operators,
    binary_LTL_operators,
    simplify_issy_formula_with_math,
)

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


@generate
def issy_parser():
    vars = yield parsec.many(try_choice(macro, var_dec_parser) << spaces())
    objectives = yield parsec.many(formula_parser)

    yield spaces()
    games = yield parsec.many(issy_game_parser)
    return vars, objectives, games


@generate
def macro():
    x = yield try_choice(macro_val, macro_expr)
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
    expr = yield expr_parser
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
def uni_expr_parser():
    op = yield regex("(!|-)")
    yield spaces()
    first = yield expr_parser
    yield spaces()
    if op == "-":
        return create_neg_no(first)
    else:
        return create_uniop("!", first)


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
    left = yield primary_expr_parser
    op = yield parsec.optional(regex("(>=|<=|>|<|!=|=)") << spaces())
    if op:
        right = yield primary_expr_parser
        return create_mathrel(left, op, right)
    return left


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
    input_wo_comments = re.sub("//.*(\n|$)", "", input)
    global file_name
    file_name = name_str
    vars_or_macros, objectives, games = (parser << parsec.eof()).parse(
        input_wo_comments
    )
    program, ltl_spec = process(name_str, vars_or_macros, objectives, games)

    return program, ltl_spec


def process(
    name_str, vars_or_macros, formula_objectives, games
) -> tuple[Program, Formula]:
    old_dual = config.Config.getConfig().dual
    config.Config.getConfig().dual = False
    con_vars = set()
    lose_var = None

    # process vars
    # build symbol table
    # separate inputs and state vars
    debug = config.Config.getConfig().debug
    inputs = []
    state_vars = []
    next_state_vars = []
    macros = [v for v in vars_or_macros if len(v) == 2]

    macros = {Variable(k): v for k, v in macros}
    macros = {k: saturate_macros(v, macros) for k, v in macros.items()}

    formula_objectives = list(
        map(lambda a: a.replace_formulas(macros), formula_objectives)
    )
    new_formula_objectives = []
    for a in formula_objectives:
        preds = atomic_predicates(a)
        to_replace = {}
        if len(to_replace.keys()) > 0:
            formula_objectives.append(a.replace_formulas(to_replace))
        else:
            new_formula_objectives.append(a)
    formula_objectives = new_formula_objectives

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
                next_state_vars.append(next_var)
                symbol_table[str(v)] = type
                symbol_table[str(next_var)] = type
            case _:
                raise Exception("Unknown var kind: " + str(kind))

    parts_to_sub_programs = []
    states_to_exclude_minigame = {}
    if len(games) == 0:
        raise Exception("We do not handle ISSY files without game arenas yet.")
        program = Program(
            name_str,
            {"eval"},
            "eval",
            [(str(v), symbol_table[str(v)]) for v in state_vars],
            [
                Transition(
                    "eval",
                    true(),
                    [BiOp(v, "=", NonDeterministic()) for v in state_vars],
                    [],
                    "eval",
                )
            ],
            [(v, symbol_table[str(v)]) for v in inputs],
            [],
        )
        states_to_exclude_minigame[0] = []
        objective = true()
        losing_states = []
        parts_to_sub_programs.append((program, objective, losing_states))
    else:
        game_parts = independent_games(inputs + state_vars, games)

        # TODO:
        #   get all predicates in each game transition
        #   filter out updates
        #   filter out updates that are only ever assigned values
        #   and are never used in normal predicates in the game, or in the formula
        #   then we turn these into boolean propositions an give them to controller directly
        #   this can be done at level of program too in general,
        #   but doing it here reduces update combination explosion

        for i, game_part in enumerate(game_parts):
            # process games separately, treat common variables as internal state vars
            # problem: program will complete action sets automatically
            # then combine trans
            # and add mini-games to handle unset vars
            # maybe add feature to program, so that we have x := * as actions
            # this triggers adding mini-game to set x to any value.
            # and x := cond(x), such that mini-game always ends in a state with cond(x) true
            # NOTE: if unset var not used in guard then no need to add mini-game

            all_trans_conds = [t[1] for g in game_part for t in g[3]]
            updates_to_con_props, new_con_props = booleanise_strict_updates(
                all_trans_conds, formula_objectives
            )
            symbol_table.update({str(v): BOOLEAN for v in new_con_props})
            con_vars.update(new_con_props)

            for game in game_part:
                game_index = len(parts_to_sub_programs)
                states_to_exclude_minigame[game_index] = set()
                vars_updates_depend_on_in_game = set()
                game_type, init, locs_in_game, transitions = game

                marked_states = {}
                locs = set()
                state_to_new_state = {}
                for v, kind, type in locs_in_game:
                    new_state = "game_" + str(game_index) + "_state_" + v.name
                    state_to_new_state[v.name] = new_state
                    locs.add(new_state)
                    if type in marked_states.keys():
                        marked_states[type].append(Variable(new_state))
                    else:
                        marked_states[type] = [Variable(new_state)]

                init = state_to_new_state[init]

                raw_transitions = {
                    state_to_new_state[src]: [] for src, _, _ in transitions
                }
                transitions = [
                    (
                        src,
                        f.replace_formulas(macros).replace_formulas(
                            updates_to_con_props
                        ),
                        tgt,
                    )
                    for src, f, tgt in transitions
                ]

                vars_in_game = {
                    v if not v.is_next() else v.prev_rep()
                    for _, f, _ in transitions
                    for v in f.variablesin()
                    if v not in inputs
                }
                vars_in_game.difference_update(con_vars)
                for old_src, orig_formula, old_tgt in transitions:
                    src = state_to_new_state[old_src]
                    tgt = state_to_new_state[old_tgt]
                    orig_formula = orig_formula.replace_formulas(macros)

                    print(str(orig_formula))
                    formula = only_dis_or_con_junctions(
                        propagate_negations(strip_mathexpr(orig_formula))
                    )
                    print(str(formula))
                    cond_updates = formula_to_transitions(formula, inputs, symbol_table)

                    for res in cond_updates:
                        if res is None:
                            continue
                        cond, raw_update_sets = res
                        for raw_updates in raw_update_sets:
                            predicate_upgrades = []
                            updates = []
                            for raw_update in raw_updates:
                                f = strip_mathexpr(raw_update)
                                if isinstance(f, BiOp) and f.op == "=":
                                    # TODO: normalise to prime variables on left and others on right
                                    left, right = f.left, f.right
                                    if (
                                        isinstance(left, Variable)
                                        and left.is_next()
                                        and not any(
                                            v
                                            for v in right.variablesin()
                                            if v.is_next()
                                        )
                                    ):
                                        updates.append(
                                            create_update(left.prev_rep(), right)
                                        )
                                        vars_updates_depend_on_in_game.update(
                                            right.variablesin()
                                        )
                                        continue

                                next_vars_in_update = [
                                    v for v in raw_update.variablesin() if v.is_next()
                                ]
                                if len(next_vars_in_update) > 1:
                                    raise Exception(
                                        "We do not yet handle updates with multiple next-state variables: "
                                        + str(raw_update)
                                    )
                                predicate_upgrades.append(raw_update)

                            # Before adding, need to resolve determinism in transitions in favour of controller
                            # Maybe, this should be a feature added at program level? Would also need to allow updates at LTL level
                            # So that LTLMT formulas can be replaced appropriately
                            # Would prevent replication of this logic in multiple parsers
                            # For now we do it here
                            vars_updated_in_transition = {u.left for u in updates}

                            vars_not_updated = vars_in_game - vars_updated_in_transition

                            # need to add keep updates for vars not in combination
                            for v in vars_not_updated:
                                updates.append(BiOp(v, "=", NonDeterministic()))

                            t = Transition(
                                src,
                                cond,
                                updates,
                                [],
                                tgt,
                            )
                            t.set_predicate_upgrades(predicate_upgrades)
                            raw_transitions[src].append(t)

                # need to detect when transitions from same src have non-mutually exclusive conditions, and in that case
                # create binary variables to distinguish them, and give them to controller
                new_transitions, lose_transitions, new_con_vars = determinise(
                    raw_transitions, game_index, symbol_table
                )
                symbol_table.update({str(v): BOOLEAN for v in new_con_vars})
                con_vars.update(new_con_vars)
                if len(lose_transitions) > 0:
                    lose_var = "lose"
                    states_to_exclude_minigame[game_index].add(lose_var)
                # Now, we have processed the transitions, and added nondets
                # we need to build programs
                # do cross product, while taking into account predicate upgrades, and accordingly add mini-games

                # build program for this game
                # need to massage vars according to expected format
                program = Program(
                    name_str + "_part_" + str(i),
                    locs,
                    init,
                    [(str(v), symbol_table[str(v)]) for v in vars_in_game],
                    new_transitions + lose_transitions,
                    [(v, symbol_table[str(v)]) for v in inputs],
                    [(v, BOOLEAN) for v in con_vars],
                )
                print(program.to_prog(""))
                if not program.deterministic:
                    raise Exception("Program from ISSY parsing is not deterministic.")

                marked_states = {
                    i: {ss for ss in s if str(ss) in program.states}
                    for i, s in marked_states.items()
                }

                losing_states = []

                match game_type:
                    case "Buechi":
                        objective_states = disjunct_formula_set(marked_states[1])
                        objective = G(F(objective_states))
                    case "Safety":
                        objective_states = disjunct_formula_set(marked_states[1])
                        if len(marked_states[1]) == (
                            len(program.states)
                            if len(lose_transitions) == 0
                            else len(program.states) - 1
                        ):
                            objective = true()
                        else:
                            objective = G(objective_states)
                            losing_states_here = [
                                s
                                for s in program.states
                                if Variable(s) not in marked_states[1]
                            ]
                            losing_states.extend(losing_states_here)
                            states_to_exclude_minigame[game_index].update(
                                losing_states_here
                            )
                    case "Reachability":
                        objective_states = disjunct_formula_set(marked_states[1])
                        objective = F(objective_states)
                    case "ParityMaxOdd":
                        objective = parity_objective(marked_states)
                    case _:
                        raise Exception("Unknown game type: " + str(game_type))

                if len(lose_transitions) > 0:
                    objective = conjunct(
                        objective,
                        G(neg(Variable("lose"))),
                    )
                # if there are multiple games in a part, here need to add the cross product of transitions (and combine objectives)
                parts_to_sub_programs.append(
                    (
                        program,
                        objective,
                        losing_states,
                    )
                )

    # when len(parts_to_sub_programs) > 1, we either:
    #   1. perform cross-product of games (and combine objectives)
    #   2. perform interleaving of games (and modify objective accordingly)
    # For now we perform cross-product of games
    #   1. Create program for each game
    #   2. Create cross-product of programs
    #   3. Figure out objective for combined program
    to_replace = {}
    if len(parts_to_sub_programs) == 1:
        program = parts_to_sub_programs[0][0]
        game_objectives = [parts_to_sub_programs[0][1]]
        losing_states = {0: parts_to_sub_programs[0][2]}
        if len(losing_states[0]) > 0:
            lose_var = "lose"
        else:
            lose_var = None
        preds_to_replace = {}
        to_exclude_from_minigame = states_to_exclude_minigame[0]
    else:
        symbol_table.update({str(v): BOOLEAN for v in con_vars})
        losing_states = {
            i: parts_to_sub_programs[i][2] for i in range(len(parts_to_sub_programs))
        }
        if not lose_var and any(i for i, ls in losing_states.items() if len(ls) > 0):
            lose_var = "lose"

        program, prog_old_to_new_state = program_cross_product(
            [p for p, _, _ in parts_to_sub_programs],
            symbol_table,
            losing_states,
            lose_var,
            name_str,
        )
        print(program.to_prog(""))
        prog_old_to_new_state = {
            i: {
                old_s: [s for s in ss if str(s) in program.states]
                for old_s, ss in prog_old_to_new_state[i].items()
            }
            for i in prog_old_to_new_state.keys()
        }
        to_replace.update(prog_old_to_new_state)
        game_objectives = [
            obj.replace(
                {
                    s: disjunct_formula_set(new_ss)
                    for s, new_ss in prog_old_to_new_state[i].items()
                }
            )
            for i, (_, obj, _) in enumerate(parts_to_sub_programs)
        ]
        to_exclude_from_minigame = [
            str(new_s)
            for i, ss in states_to_exclude_minigame.items()
            for s in ss
            for new_s in prog_old_to_new_state[i][Variable(s)]
        ]
        if lose_var:
            to_exclude_from_minigame.append(lose_var)

    if old_dual:
        config.Config.getConfig().dual = old_dual
        print(str(config.Config.getConfig().dual))

    preds_to_replace_in_ltl, non_det_v, new_con_props = extract_formula_updates(
        program, conjunct_formula_set(formula_objectives)
    )
    if len(non_det_v) > 0:
        new_trans = []
        for t in program.transitions:
            new_actions = t.action
            for v in non_det_v:
                new_actions.append(BiOp(v.prev_rep(), "=", NonDeterministic()))
            new_t = Transition(t.src, t.condition, new_actions, t.outputs, t.tgt)
            new_trans.append(new_t)
        program.transitions = new_trans

    new_formula_objectives = []
    for o in formula_objectives:
        new_o = o.replace_formulas(preds_to_replace_in_ltl)
        preds_in_new_o = atomic_predicates(new_o)
        to_project_into_next = {}
        for p in preds_in_new_o:
            if any(v for v in p.variablesin() if v.is_next()):
                to_project_into_next[p] = X(p.prev_rep())
        new_o = new_o.replace_formulas(to_project_into_next)
        new_formula_objectives.append(new_o)
    formula_objectives = new_formula_objectives

    to_replace.update(preds_to_replace_in_ltl)

    if len(new_con_props) > 0:
        for v in new_con_props:
            program.symbol_table[str(v)] = BOOLEAN
            program.con_events.append((v, BOOLEAN))

    # we do not need to add minigames at some states:
    # if goal is safety: no need to add minigames at unsafe states
    # (not handled yet) if goal is reachability: no need to add minigames from states that cannot reach goal
    program, preds_to_replace, minigame_states = fill_in_minigames(
        program, formula_objectives, to_exclude_from_minigame
    )

    if len(minigame_states) > 0:
        not_in_minigame = neg(disjunct_formula_set(minigame_states))
        formula_objectives = list(
            map(lambda x: massage_ltl(x, not_in_minigame, {}), formula_objectives)
        )
        minigame_safety = G(F(neg(disjunct_formula_set(minigame_states))))
        new_game_objectives = [minigame_safety]
    else:
        new_game_objectives = []

    there_is_safety_game = False
    for game_obj in game_objectives:
        if (
            isinstance(game_obj, UniOp)
            and game_obj.op == "G"
            and not (isinstance(game_obj.right, UniOp) and game_obj.right.op == "F")
        ):
            f = game_obj.right
            f = disjunct_formula_set([f] + minigame_states)
            new_game_objectives.append(G(f))
            there_is_safety_game = True
        else:
            new_game_objectives.append(game_obj)

    if not there_is_safety_game and lose_var:
        new_game_objectives.append(G(neg(Variable(lose_var))))

    game_objectives = new_game_objectives

    game_objectives_f = conjunct_formula_set(game_objectives)
    replace_in_ltl = lambda f: (
        f.replace_formulas(preds_to_replace) if len(preds_to_replace.keys()) > 0 else f
    )

    if len(formula_objectives) == 0:
        new_objective = game_objectives_f
    else:
        new_objective = conjunct_formula_set(
            [replace_in_ltl(o) for o in formula_objectives]
            + [game_objectives_f]
            # [
            #     BiOp(
            #         massage_ltl(o.left),
            #         "->",
            #         conjunct(massage_ltl(o.right), game_objectives_f),
            #     )
            #     for o in formula_objectives
            # ]
        )

    refine_init_values(program, conjunct_formula_set(formula_objectives))
    if len(game_objectives) == 0:
        f = neg(conjunct_formula_set(formula_objectives))
        f = normalize_ltl(propagate_negations(f))
        _, fixed_values = extract_initial_values(
            set(Variable(v) for v in program.unset_init_vars),
            f,
            program.symbol_table,
        )
        for var, val in fixed_values.items():
            program.init_var_values[str(var)] = val
            program.unset_init_vars.remove(str(var))
    print(program.to_prog(new_objective))
    return program, new_objective


def extract_formula_updates(program, formula_objective):
    preds_to_replace = {}
    to_add_non_det_trans = set()
    new_con_props = set()

    preds = atomic_predicates(formula_objective)
    for p in preds:
        p = strip_mathexpr(p)
        unk_next_vars_in_p = [
            v
            for v in p.variablesin()
            if v.is_next() and v.prev_rep().name not in program.symbol_table.keys()
        ]
        if len(unk_next_vars_in_p) != 1:
            to_add_non_det_trans.update(unk_next_vars_in_p)
        else:
            v = unk_next_vars_in_p[0]
            # we are looking for two forms: variable, or assignment to constant
            if isinstance(p, Variable):  ## i.e. p is a boolean
                preds_to_replace[v] = X(v.prev_rep())
                new_con_props.add(v.prev_rep())
            elif isinstance(p, BiOp):
                if p.op == "!=":
                    new_p = BiOp(p.left, "=", p.right)
                    preds_to_replace[p] = neg(new_p)
                    p = new_p
                elif p.op != "=":
                    to_add_non_det_trans.update(unk_next_vars_in_p)
                    continue

                var = p.left if isinstance(p.left, Variable) else p.right
                val = p.right if var == p.left else p.left
                if isinstance(val.val, BoolAtoms):
                    if val.val == BoolAtoms.TRUE:
                        preds_to_replace[p] = X(var.prev_rep())
                    else:
                        preds_to_replace[p] = neg(X(var.prev_rep()))
                    new_con_props.add(var.prev_rep())

                elif any(
                    p1
                    for p1 in preds
                    for v in unk_next_vars_in_p
                    if v.prev_rep() in p1.variablesin()
                ):
                    to_add_non_det_trans.update(unk_next_vars_in_p)
                else:
                    # here we have assignments to constants, e.g. x' = 0
                    var = Variable("game_con_" + stringify_pred(p).name)
                    preds_to_replace[p] = X(var)
                    preds_to_replace[MathExpr(p)] = X(var)
                    new_con_props.add(var.prev_rep())
            else:
                to_add_non_det_trans.update(unk_next_vars_in_p)

    return preds_to_replace, to_add_non_det_trans, new_con_props


def determinise(raw_transitions: dict[str, list[Transition]], game_index, symbol_table):
    con_vars = set()
    debug = config.Config.getConfig().debug
    new_transitions = []
    lose_transitions = []
    for src, trans in raw_transitions.items():
        print("trans: " + "\n".join(map(str, trans)))
        equiv_map, sat_map, equiv_parts, _ = condition_choices(trans, symbol_table)
        new_src_trans = []
        equiv_index = 0
        sat_index = 0

        eq_trigger_to_add = {t: [] for t in trans}
        sat_trigger_to_add = {t: [] for t in trans}
        for t, equiv_part_minus_t in equiv_map.items():
            raw_equiv_triggers = [
                Variable("equiv_" + str(no))
                for no in range(0, len(equiv_part_minus_t) + 1)
            ]
            eq_con_events, equiv_binary_map = binary_rep(
                raw_equiv_triggers,
                "eq_con_" + str(game_index) + "_" + str(equiv_index) + "_",
                printing=False,
            )
            equiv_index += 1
            con_vars.update(eq_con_events)
            eq_trigger_to_add[t].append(equiv_binary_map[raw_equiv_triggers[0]])
            for i, tt in enumerate(equiv_part_minus_t):
                eq_trigger_to_add[tt].append(
                    equiv_binary_map[raw_equiv_triggers[i + 1]]
                )

        # order is important here
        # for t = trans[n], sat_map[t] only contains sat tt in trans[n + 1:]
        for t in trans:
            if t in sat_map.keys():
                if len(sat_map[t]) == 0 or t in equiv_parts.keys():
                    continue

                ts_to_distinguish = set()
                for _t in sat_map[t]:
                    if _t in equiv_parts.keys():
                        ts_to_distinguish.add(equiv_parts[_t])
                    else:
                        ts_to_distinguish.add(_t)
                ts_to_distinguish = list(ts_to_distinguish)

                if debug:
                    if t in equiv_map.keys():
                        for tt in equiv_map[t]:
                            if tt in sat_map.keys():
                                raise Exception(
                                    "Later equiv transition also in sat map"
                                )
                                # sat_map[tt] = [
                                #     _t
                                #     for _t in sat_map[tt]
                                #     if _t not in ts_to_distinguish
                                # ]
                                # if len(sat_map[tt]) == 0:
                                del sat_map[tt]

                raw_sat_triggers = [
                    Variable("sat_" + str(no))
                    for no in range(0, len(ts_to_distinguish) + 1)
                ]
                sat_con_events, sat_binary_map = binary_rep(
                    raw_sat_triggers,
                    "sat_con_" + str(game_index) + "_" + str(sat_index) + "_",
                    printing=False,
                )
                sat_index += 1
                con_vars.update(sat_con_events)

                one_of_the_rest = disjunct_formula_set(
                    {tt.condition for tt in ts_to_distinguish}
                )

                # need to add below trans also to equiv transitions
                equiv_to_t = [t]
                if t in equiv_map.keys():
                    equiv_to_t.extend(equiv_map[t])
                elif t in equiv_parts.keys():
                    equiv_to_t.extend(equiv_map[equiv_parts[t]])

                if len(equiv_to_t) > 1:
                    if not is_tautology(one_of_the_rest, symbol_table):
                        if not sat(
                            conjunct(t.condition, neg(one_of_the_rest)),
                            symbol_table,
                        ):
                            for eq_t in equiv_to_t:
                                sat_trigger_to_add[eq_t].append(
                                    sat_binary_map[raw_sat_triggers[0]]
                                )
                                if debug and not sat(
                                    conjunct_formula_set(sat_trigger_to_add[eq_t]),
                                    symbol_table | {str(v): BOOLEAN for v in con_vars},
                                ):
                                    raise Exception(
                                        "In processing transitions from state "
                                        + str(src)
                                        + ", could not distinguish transition: \n"
                                        + str(t)
                                    )
                        else:
                            none_of_the_rest = neg(one_of_the_rest)
                            trigger_cond = disjunct(
                                none_of_the_rest,
                                conjunct(
                                    one_of_the_rest,
                                    sat_binary_map[raw_sat_triggers[0]],
                                ),
                            )
                            for eq_t in equiv_to_t:
                                sat_trigger_to_add[eq_t].append(trigger_cond)
                    else:
                        for eq_t in equiv_to_t:
                            sat_trigger_to_add[eq_t].append(
                                sat_binary_map[raw_sat_triggers[0]]
                            )
                            if debug and not sat(
                                conjunct_formula_set(sat_trigger_to_add[eq_t]),
                                symbol_table | {str(v): BOOLEAN for v in con_vars},
                            ):
                                raise Exception(
                                    "In processing transitions from state "
                                    + str(src)
                                    + ", could not distinguish transition: \n"
                                    + str(t)
                                )

                if len(ts_to_distinguish) > 0:
                    if len(equiv_to_t) == 1:
                        sat_trigger_to_add[t].append(
                            sat_binary_map[raw_sat_triggers[0]]
                        )
                    for i, tt in enumerate(ts_to_distinguish):
                        equiv_to_tt = [tt]
                        if tt in equiv_map.keys():
                            equiv_to_tt.extend(equiv_map[tt])
                        elif tt in equiv_parts.keys():
                            equiv_to_tt.extend(equiv_map[equiv_parts[tt]])

                        one_of_the_rest = disjunct_formula_set(
                            {ttt.condition for ttt in ts_to_distinguish if ttt != tt}
                            | {t.condition}
                        )
                        if not is_tautology(one_of_the_rest, symbol_table):
                            if not sat(
                                conjunct(tt.condition, neg(one_of_the_rest)),
                                symbol_table,
                            ):
                                for eq_tt in equiv_to_tt:
                                    sat_trigger_to_add[eq_tt].append(
                                        sat_binary_map[raw_sat_triggers[i + 1]]
                                    )
                                    if debug and not sat(
                                        conjunct_formula_set(sat_trigger_to_add[eq_tt]),
                                        symbol_table
                                        | {str(v): BOOLEAN for v in con_vars},
                                    ):
                                        raise Exception(
                                            "In processing transitions from state "
                                            + str(src)
                                            + ", could not distinguish transition: \n"
                                            + str(t)
                                        )
                            else:
                                none_of_the_rest = neg(one_of_the_rest)
                                trigger_cond = disjunct(
                                    none_of_the_rest,
                                    conjunct(
                                        one_of_the_rest,
                                        sat_binary_map[raw_sat_triggers[i + 1]],
                                    ),
                                )
                                for eq_tt in equiv_to_tt:
                                    sat_trigger_to_add[eq_tt].append(trigger_cond)
                                    if debug and not sat(
                                        conjunct_formula_set(sat_trigger_to_add[eq_tt]),
                                        symbol_table
                                        | {str(v): BOOLEAN for v in con_vars},
                                    ):
                                        raise Exception(
                                            "In processing transitions from state "
                                            + str(src)
                                            + ", could not distinguish transition: \n"
                                            + str(t)
                                        )
                        else:
                            for eq_tt in equiv_to_tt:
                                sat_trigger_to_add[eq_tt].append(
                                    sat_binary_map[raw_sat_triggers[i + 1]]
                                )
                                if debug and not sat(
                                    conjunct_formula_set(sat_trigger_to_add[eq_tt]),
                                    symbol_table | {str(v): BOOLEAN for v in con_vars},
                                ):
                                    raise Exception(
                                        "In processing transitions from state "
                                        + str(src)
                                        + ", could not distinguish transition: \n"
                                        + str(t)
                                    )

        for t in trans:
            trigger_condition = conjunct_formula_set(
                eq_trigger_to_add[t] + sat_trigger_to_add[t]
            )

            new_t = Transition(
                t.src,
                conjunct(
                    t.condition,
                    trigger_condition,
                ),
                t.action,
                [],
                t.tgt,
            )
            new_t.set_predicate_upgrades(t.pred_upgrades)
            new_src_trans.append(new_t)

        new_transitions.extend(new_src_trans)
        no_trans_triggered = neg(
            disjunct_formula_set(t.condition for t in new_src_trans)
        )
        if sat(
            no_trans_triggered,
            symbol_table | {str(v): BOOLEAN for v in con_vars},
        ):
            lose_transitions.append(Transition(src, no_trans_triggered, [], [], "lose"))

        if debug:
            for t in new_transitions + lose_transitions:
                for tt in new_transitions + lose_transitions:
                    if t == tt or t.src != tt.src:
                        continue
                    if sat(
                        conjunct(t.condition, tt.condition),
                        symbol_table | {str(v): BOOLEAN for v in con_vars},
                    ):
                        raise Exception(
                            "After processing, transitions from state "
                            + str(src)
                            + " still have non-distinguishable conditions: \n"
                            + str(t)
                            + "\n"
                            + str(tt)
                        )

    return new_transitions, lose_transitions, con_vars


def condition_choices(transitions: List[Transition], symbol_table) -> tuple[
    dict[Transition, list[Transition]],
    dict[Transition, list[Transition]],
    dict[Transition, Transition],
    Optional[Formula],
]:
    # returns two mappings and an optional condition:
    # 1) transitions grouped with others that have equivalent conditions
    # 2) transitions mapped to others with satisfiable (but non-equivalent) conditions
    # 3) an optional condition returned when the transitions are not complete w.r.t. pre-state,
    # the condition describes when no transition is triggerable

    equiv_map: dict[Transition, list[Transition]] = {}
    compat_map: dict[Transition, list[Transition]] = {}

    equiv_parts: dict[Transition, Transition] = {}
    n = len(transitions)
    found_equiv = set()
    for i in range(n):
        t_i = transitions[i]
        cond_i = t_i.condition
        # if we already found equivalent transitions for t_i, skip
        # it's satisfiability and equivalence with others has already been handled
        if t_i in found_equiv:
            continue
        for j in range(i + 1, n):
            t_j = transitions[j]
            if t_j in found_equiv:
                continue

            cond_j = t_j.condition
            if sat(conjunct(cond_i, cond_j), symbol_table):
                if sat(conjunct(cond_i, neg(cond_j)), symbol_table) or sat(
                    conjunct(cond_j, neg(cond_i)), symbol_table
                ):
                    compat_map.setdefault(t_i, list()).append(t_j)
                else:
                    equiv_map.setdefault(t_i, list()).append(t_j)
                    found_equiv.add(t_j)
                    equiv_parts[t_j] = t_i
    no_trans_triggered = neg(disjunct_formula_set(t.condition for t in transitions))
    if not sat(no_trans_triggered, symbol_table):
        no_trans_triggered = None
    return equiv_map, compat_map, equiv_parts, no_trans_triggered


def independent_games(vars, games):
    if len(games) == 1:
        return [games]

    vars_to_games = {}
    for i, s in enumerate(vars):
        vars_to_games[str(s)] = []

    # detect dependence based on vars used in transitions
    def get_vars_in_game(i):
        game = games[i]
        vars_in_game = set()
        _, _, _, transitions = game
        for _, formula, _ in transitions:
            for v in formula.variablesin():
                if v.is_next():
                    vars_in_game.add(str(v.prev_rep()))
                else:
                    vars_in_game.add(str(v))
        return vars_in_game

    for i in range(len(games)):
        vars_in_game = get_vars_in_game(i)
        for v in vars_in_game:
            if v in vars_to_games.keys():
                vars_to_games[v].append(i)

    # transitively collect games based on shared variables
    visited_games = set()
    independent_game_sets = []

    for i in range(len(games)):
        if i in visited_games:
            continue
        to_visit = [i]
        current_set = set()

        while to_visit:
            current_game = to_visit.pop()
            if current_game in visited_games:
                continue
            visited_games.add(current_game)
            current_set.add(current_game)

            vars_in_current_game = get_vars_in_game(current_game)
            for v in vars_in_current_game:
                for dependent_game in vars_to_games[v]:
                    if dependent_game not in visited_games:
                        to_visit.append(dependent_game)

        independent_game_sets.append(list(current_set))
    return list(map(lambda s: list(map(lambda g: games[g], s)), independent_game_sets))


def normalise_update(f):
    updates = []
    to_replace = {}
    if isinstance(u := f, Variable):
        updates.append(BiOp(u, "=", true()))
        updates.append(BiOp(u, "=", false()))
        to_replace[u] = BiOp(u, "=", true())
        to_replace[neg(u)] = BiOp(u, "=", false())
    elif isinstance(u, UniOp):
        return normalise_update(u)
    elif isinstance(u, BiOp):
        if (
            isinstance(u.left, Variable)
            and isinstance(u.right, Value)
            and isinstance(u.right, BoolAtoms)
        ):
            return normalise_update(u.left)
        elif (
            isinstance(u.right, Variable)
            and isinstance(u.left, Value)
            and isinstance(u.left, BoolAtoms)
        ):
            return normalise_update(u.right)
        elif u.op == "!=":
            updates, to_replace = normalise_update(BiOp(u.left, "=", u.right))
            to_replace[MathExpr(u)] = neg(BiOp(u.left, "=", u.right))
            to_replace[u] = neg(BiOp(u.left, "=", u.right))
        else:
            updates.append(u)
    return updates, to_replace


def handle_update_partition(updates, symbol_table):
    var_to_update = {}
    for u in updates:
        var = next(x for x in u.variablesin() if x.is_next())
        var_to_update.setdefault(str(var), set()).add(u)

    # TODO: some partitions may have to be separated further, given non equality updates
    partitions = partition_updates(var_to_update, [])
    new_partitions = []
    for part in partitions:
        refined_parts = refine_partition(part, var_to_update, symbol_table)
        new_partitions.extend(refined_parts)
    partitioned_updates = new_partitions
    update_combinations = cross_product_of_partitions(partitioned_updates)
    return update_combinations


def cross_product_of_partitions(partitions):
    # croos product of partitions, up to negation (non-inclusion)
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


def refine_partition(part, var_to_update, symbol_table):
    # we refine partition based on mutual exclusivity of updates
    refined_parts = []
    updates_in_part = itertools.chain.from_iterable([var_to_update[v] for v in part])
    # we check mutual exclusivity pairwise between each update in updates_in_part
    # and partition them into partitions, such that partitions contain mutually exclusive updates
    for u in updates_in_part:
        placed = False
        for rp in refined_parts:
            if all(
                not sat(
                    conjunct(u, u2),
                    symbol_table,
                )
                for u2 in rp
            ):
                rp.append(u)
                placed = True
                break
        if not placed:
            refined_parts.append([u])
    return refined_parts


def booleanise_strict_updates(trans_in_all_games, formula_objectives):
    preds_to_replace = {}
    new_con_props = set()
    old_to_new = {}
    v_to_type = {}

    preds = atomic_predicates(conjunct_formula_set(trans_in_all_games))
    all_updates = {p for p in preds if any(v for v in p.variablesin() if v.is_next())}
    non_update_preds = (
        preds | atomic_predicates(conjunct_formula_set(formula_objectives))
    ).difference(all_updates)
    vars_in_non_updates = {v for p in non_update_preds for v in p.variablesin()}
    current_vars_in_updates = {
        v for p in all_updates for v in p.variablesin() if not v.is_next()
    }
    for p in all_updates:
        p = strip_mathexpr(p)
        unk_next_vars_in_p = [v for v in p.variablesin() if v.is_next()]
        if len(unk_next_vars_in_p) == 1:
            v = unk_next_vars_in_p[0]
            if (
                v.prev_rep() in vars_in_non_updates
                or v.prev_rep() in current_vars_in_updates
            ):
                continue
            # we are looking for two forms: variable, or assignment to constant
            if isinstance(p, Variable):  ## i.e. p is a boolean
                preds_to_replace[v] = v.prev_rep()
                new_con_props.add(v.prev_rep())
            elif isinstance(p, BiOp):
                original_p = p
                if p.op == "!=":
                    new_p = BiOp(p.left, "=", p.right)
                    preds_to_replace[p] = neg(new_p)
                    p = new_p
                elif p.op != "=":
                    continue

                var = p.left if isinstance(p.left, Variable) else p.right
                val = p.right if var == p.left else p.left
                if not isinstance(val, Value):
                    # TODO: if sum over variables we can deal with this
                    continue
                if isinstance(val.val, BoolAtoms):
                    v_to_type[v] = BOOLEAN
                    if val.val == BoolAtoms.TRUE:
                        preds_to_replace[original_p] = var.prev_rep()
                        old_to_new.setdefault(v, set()).add(
                            (original_p, var.prev_rep())
                        )
                    else:
                        preds_to_replace[original_p] = neg(var.prev_rep())
                        old_to_new.setdefault(v, set()).add(
                            (original_p, var.prev_rep())
                        )
                    new_con_props.add(var.prev_rep())
                else:
                    v_to_type[v] = INTEGER
                    # here we have assignments to constants, e.g. x' = 0
                    var = Variable("game_con_" + stringify_pred(p).name)
                    preds_to_replace[original_p] = var
                    preds_to_replace[MathExpr(original_p)] = var
                    old_to_new.setdefault(v, set()).add((original_p, var))
                    new_con_props.add(var)

    more_than_one_update_vars = {
        v: old_to_new[v] for v in old_to_new.keys() if len(old_to_new[v]) > 1
    }

    for v, change in more_than_one_update_vars.items():
        old_vars = list(map(lambda x: x[1], change))
        if v_to_type[v] == INTEGER:
            old_vars.append(neg(conjunct_formula_set(old_vars)))
        bin_vars, rep = binary_rep(
            old_vars,
            "game_con_" + v.prev_rep().name,
            printing=True,
        )
        new_con_props.update(bin_vars)
        for old_p, new_p in change:
            new_con_props.difference_update(new_p.variablesin())
            preds_to_replace[old_p] = new_p.replace_formulas(rep)
            preds_to_replace[MathExpr(old_p)] = new_p.replace_formulas(rep)

    return preds_to_replace, new_con_props


def extract_updates_from_formula(formula):
    preds = atomic_predicates(formula)
    updates = set()
    to_replace = {}
    for f in preds:
        if any(v for v in f.variablesin() if v.is_next()):
            norm_updates, norm_to_replace = normalise_update(strip_mathexpr(f))
            updates.update(norm_updates)
            to_replace.update(norm_to_replace)
    return updates, to_replace


def formula_to_transitions(formula, inputs, symbol_table):
    formula = almost_dnf_to_dnf(formula, 3)
    if config.Config.getConfig().debug:
        if sat(
            conjunct(neg(formula), almost_dnf_to_dnf(formula, 3)),
            symbol_table,
        ) and sat(
            conjunct(formula, neg(almost_dnf_to_dnf(formula, 3))),
            symbol_table,
        ):
            raise Exception(
                "Wrong translation from almost dnf to dnf: "
                + str(formula)
                + " vs "
                + str(almost_dnf_to_dnf(formula, 3))
            )

    disjuncts = []
    # TODO: also handle almost-DNF formulas of form (CONJ & CONJ) & (DISJ | DISJ | ...)
    if (is_dnf(formula) or (isinstance(formula, BiOp) and formula.op == "|")) and any(
        v for v in formula.variablesin() if v.is_next()
    ):
        if isinstance(formula, BiOp) and formula.op == "|":
            disjuncts.extend(formula.sub_formulas_up_to_associativity())
        else:
            disjuncts.append(formula)
    else:
        disjuncts.append(formula)

    results = []
    for d in disjuncts:
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

        if is_conjunction_of_atoms(d):
            preds = d.sub_formulas_up_to_associativity() if isinstance(d, BiOp) else [d]
            update_preds = {
                p for p in preds if any(v for v in p.variablesin() if v.is_next())
            }
            cond_preds = conjunct_formula_set(p for p in preds if p not in update_preds)
            results.append((cond_preds, frozenset(update_preds)))
        else:
            # TODO: this can be optimized further by not generating all combinations
            #       but only equality updates, and reduced up to negation
            results.extend(
                generate_update_combinations(d, updates, inputs, symbol_table)
            )

    return process_cond_updates(results, inputs, symbol_table)


def process_cond_updates(results, inputs, symbol_table):
    trans = {}
    cond_to_u = {}
    for r in results:
        if r is None:
            continue
        cond, u = r
        if not sat(cond, symbol_table):
            continue
        new_cond, new_u = clean_updates(u, inputs, symbol_table)
        cond_to_u.setdefault(cond, set()).add((new_u, new_cond))

    for cond, us in trans.items():
        if len(us) > 1:
            # if there is a (u1, new_cond1) and (u2, new_cond2) in us
            # s.t., u1 is a subset of u2, and new_cond1 is None
            # then we can remove (u2, new_cond2)
            us_list = list(us)
            to_remove = set()
            for i in range(len(us_list)):
                u1, new_cond1 = us_list[i]
                for j in range(len(us_list)):
                    if i == j:
                        continue
                    u2, new_cond2 = us_list[j]
                    if new_cond1 is None and u1.is_subset_of(u2):
                        to_remove.add((u2, new_cond2))
            for r in to_remove:
                us.remove(r)

    for cond, us in cond_to_u.items():
        for u, new_cond in us:
            new_new_cond = cond if not new_cond else conjunct(cond, new_cond)
            if u in trans.keys():
                trans[u].add(new_new_cond)
            else:
                trans[u] = {new_new_cond}

    results = []
    for u, conds in trans.items():
        reduced_conds = reduce_formula_set_up_to_equivalence(conds, symbol_table)
        print("reduced up to strength: " + str(len(conds) - len(reduced_conds)))
        reduced_conds = set(
            map(
                lambda x: simplify_issy_formula_with_math(x, symbol_table),
                reduced_conds,
            )
        )
        if len(reduced_conds) > 1:
            reduced_conds_disj = join_disjuncts(reduced_conds)
            if not is_tautology(
                implies(
                    disjunct_formula_set(reduced_conds_disj),
                    disjunct_formula_set(reduced_conds),
                ),
                symbol_table,
            ) and not is_tautology(
                implies(
                    disjunct_formula_set(reduced_conds),
                    disjunct_formula_set(reduced_conds_disj),
                ),
                symbol_table,
            ):
                raise Exception(
                    "Join disjuncts produced non-equivalent formula.\n\n"
                    + str(disjunct_formula_set(reduced_conds))
                    + "\n vs \n"
                    + str(disjunct_formula_set(reduced_conds_disj))
                )
            print(
                "joined conjuncts: " + str(len(reduced_conds) - len(reduced_conds_disj))
            )

            reduced_conds = reduced_conds_disj

        new_cond, new_u = add_pred_upgrades_as_conds(u)
        results.append(
            (conjunct(new_cond, disjunct_formula_set(reduced_conds)), [new_u])
        )

    return results


def generate_update_combinations(cond, updates, inputs, symbol_table):
    update_list = list(updates)
    if len(updates) == 0:
        return [(cond, frozenset([]))]
    update_combinations = handle_update_partition(updates, symbol_table)
    # update_combinations = powerset(update_list)
    print("Number of update combinations: " + str(len(update_combinations)))

    with Pool(config.Config.getConfig().workers) as pool:
        rs = pool.map(
            handle_update_combination,
            [
                (combination, cond, update_list, inputs, symbol_table)
                for combination in update_combinations
            ],
        )
    return rs


def add_pred_upgrades_as_conds(us):
    eq_update_map = {}
    pred_upgrades = set()
    new_updates = set()
    for u in us:
        if isinstance(u, BiOp) and u.op == "=":
            left, right = u.left, u.right
            if (
                isinstance(left, Variable)
                and left.is_next()
                and not any(v for v in right.variablesin() if v.is_next())
            ):
                eq_update_map[left] = right
                new_updates.add(u)
            else:
                pred_upgrades.add(u)
        else:
            pred_upgrades.add(u)

    new_conds = []
    for p in pred_upgrades:
        next_removed = p.replace_formulas(eq_update_map)
        if not any(v for v in next_removed.variablesin() if v.is_next()):
            new_conds.append(next_removed)
        else:
            new_updates.add(next_removed)
    return conjunct_formula_set(new_conds), new_updates


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
            f_implies_r = is_tautology(implies(f, r), symbol_table)
            r_implies_f = is_tautology(implies(r, f), symbol_table)
            if f_implies_r:
                if not r_implies_f:
                    continue
                else:
                    to_remove.add(r)
            elif r_implies_f:
                is_stronger = True
                break
        if not is_stronger:
            reduced.difference_update(to_remove)
            reduced.add(f)
    return reduced


def join_disjuncts(conjunctions_of_atoms):
    # pre-process conjunction of atoms to associate conjuncts with other conjuncts s.t.
    # res[c] = (C, n) if each conjunct c' in C agrees with c on the truth value of n propositions
    # starting with the largest n found, we join each c' in C + [c],
    # s.t., we extract the shared basic conjuncts (i.e. predicates p or !p that appear in all of them), conjunct them
    # into a formula f, and reduce each c' in C + [c] by removing the shared basic conjuncts, and create a new formula
    # that is f && ((reduced c1) || ... || (reduced cn))
    # if n = 2, and c1 = {p} and c2 = {!p}, then the reduced formula is f
    conjunctions_of_atoms = set(conjunctions_of_atoms)
    while True:
        assoc_map = {}
        for c in conjunctions_of_atoms:
            for other in conjunctions_of_atoms:
                if c == other:
                    continue
                shared_basic_conjuncts = set()
                c_conjuncts = c.sub_formulas_up_to_associativity()
                other_conjuncts = other.sub_formulas_up_to_associativity()
                for cc in c_conjuncts:
                    for oc in other_conjuncts:
                        if cc == oc:
                            shared_basic_conjuncts.add(cc)
                        elif cc == neg(oc):
                            shared_basic_conjuncts.add(cc)
                n_shared = len(shared_basic_conjuncts)
                if n_shared > 0:
                    if c in assoc_map.keys():
                        if n_shared > assoc_map[c][1]:
                            assoc_map[c] = (set([other]), n_shared)
                        elif n_shared == assoc_map[c][1]:
                            assoc_map[c][0].add(other)
                    else:
                        assoc_map[c] = (set([other]), n_shared)
        if not assoc_map:
            break
        # get the entry with the largest n
        c_to_process = max(assoc_map.items(), key=lambda item: item[1][1])[0]
        others, _ = assoc_map[c_to_process]
        shared_basic_conjuncts = set()
        c_conjuncts = c_to_process.sub_formulas_up_to_associativity()
        for other in others:
            other_conjuncts = other.sub_formulas_up_to_associativity()
            for cc in c_conjuncts:
                for oc in other_conjuncts:
                    if cc == oc:
                        shared_basic_conjuncts.add(cc)
                    elif cc == neg(oc):
                        shared_basic_conjuncts.add(cc)
        shared_formula = conjunct_formula_set(shared_basic_conjuncts)
        reduced_conjuncts = []
        for conj in others | {c_to_process}:
            conj_conjuncts = set(conj.sub_formulas_up_to_associativity())
            reduced_conjuncts.append(
                conjunct_formula_set(list(conj_conjuncts - shared_basic_conjuncts))
            )
        if all(rc == false() for rc in reduced_conjuncts):
            new_formula = shared_formula
        else:
            new_formula = conjunct(
                shared_formula,
                disjunct_formula_set(reduced_conjuncts),
            )
        conjunctions_of_atoms.difference_update(others | {c_to_process})
        conjunctions_of_atoms.add(new_formula)
    return conjunctions_of_atoms


def handle_update_combination(arg):
    combination, formula, update_list, inputs, symbol_table = arg

    if not sat(conjunct_formula_set(combination), symbol_table):
        return None

    new_f_wo_false = formula.replace_formulas(
        {u: false() for u in update_list if u not in combination}
        | {MathExpr(u): false() for u in update_list if u not in combination}
    )

    bdd_simplified = bdd_simplify(new_f_wo_false.to_smt(symbol_table)[0])
    if bdd_simplified:
        simplified = fnode_to_issy_formula(bdd_simplified)
        # needs to be pre-processed as formula was pre-processed
        simplified = propagate_negations(strip_mathexpr(simplified))
        if isinstance(simplified, Value):
            return None
        us_in_new_f_wo_false = [
            u
            for u in atomic_predicates(simplified)
            if any(v for v in u.variablesin() if v.is_next())
        ]
        if len(us_in_new_f_wo_false) != len(combination):
            return None

    new_f = new_f_wo_false.replace_formulas(
        {u: true() for u in combination}
        | {MathExpr(u): false() for u in update_list if u not in combination}
    )
    if not sat(new_f, symbol_table):
        return None
    if not is_tautology(
        implies(
            conjunct(
                new_f,
                conjunct_formula_set(
                    set(combination)
                    | {neg(u) for u in update_list if u not in combination}
                ),
            ),
            formula,
        ),
        symbol_table,
    ):
        return None
    dnfed_new_f = dnf(new_f, symbol_table)
    # if new_cond:
    #     dnfed_new_f = conjunct(new_cond, dnfed_new_f)

    return dnfed_new_f, frozenset(combination)


def clean_updates(
    updates: set[Formula], inputs, symbol_table
) -> tuple[Formula, frozenset[Formula]]:
    # collect all the equality updates (x' = f)
    # if any variable has more than two equality updates
    # do quantifier elimination to identify condition that makes them equivalent
    # then we keep only of them: if there is one with input vars, keep the one with least input vars
    # else keep the one with the least vars on the RHS
    eq_updates: dict[Variable, set[Formula]] = {}
    updates = [cancel_double_negations(strip_mathexpr(u)) for u in updates]
    for u in updates:
        if isinstance(u, BiOp) and u.op == "=":
            left = u.left
            if isinstance(left, Variable) and left.is_next():
                if left not in eq_updates.keys():
                    eq_updates[left] = {u}
                else:
                    eq_updates[left].add(u)
                continue
    new_conds = []
    updates_to_remove = []
    for v, us in eq_updates.items():
        if len(us) > 1:
            # for quantifier elimination, we construct the formula
            # exists v . (u1 & u2 & ... & un)
            elim_var = [
                Symbol(str(v), BOOL if symbol_table[str(v)] == BOOLEAN else INT)
            ]
            combined = conjunct_formula_set(us)
            quant_formula = Exists(
                elim_var,
                And(*combined.to_smt(symbol_table)),
            )
            ret = quantifier_elimination(quant_formula)
            rett = fnode_to_formula(ret)
            new_conds.append(rett)

            reduced_us = [
                u
                for u in us
                if not any(v for v in u.right.variablesin() if v in inputs)
            ]

            if len(reduced_us) == 0:
                reduced_us = us

            to_keep = min(reduced_us, key=lambda u: len(u.right.variablesin()))
            updates_to_remove.extend([u for u in us if u != to_keep])

    final_updates = {u for u in updates if u not in updates_to_remove}
    return conjunct_formula_set(new_conds), frozenset(final_updates)


def sat_multi(arg):
    formulas, symbol_table = arg
    f = conjunct_formula_set(
        [formulas[0]] + list(itertools.chain.from_iterable(formulas[1]))
    )
    issat = sat(
        f,
        symbol_table,
    )
    if issat:
        print("sat: " + str(f))
    else:
        print("unsat: " + str(f))
    return formulas if issat else None


def saturate_macros(f, macros):
    changed = True
    while changed:
        changed = False
        new_f = f.replace_formulas(macros)
        if new_f != f:
            changed = True
        f = new_f
    return f
