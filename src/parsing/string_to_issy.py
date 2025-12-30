import re
import itertools
from typing import List

import parsec
from parsec import choice, generate, string, sepBy, spaces, regex, many1, try_choice

from analysis.smt_checker import bdd_simplify
import config
from parsing.string_to_rpg import parity_objective
from programs.dfa import classify_initial_values, reachable_states
from programs.program import Program, program_cross_product
from programs.transition import Transition
from programs.util import binary_rep, refine_init_values
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
from prop_lang.types.ops_and_rels import LTLUniOps
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.update_formula import UpdateFormula
from prop_lang.util import (
    atomic_predicates,
    fnode_to_formula,
    is_contradictory,
    is_tautology,
    mutually_exclusive_rules,
    strip_mathexpr,
    true,
    neg,
    conjunct,
    disjunct_formula_set,
    simplify_formula_without_math,
    conjunct_formula_set,
    implies,
    G,
    F,
    disjunct,
    sat,
    dnf,
    false,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.machines.wrapped_hoa import WrappedHOA
from synthesis.synthesis import synthesize
from parsing.string_to_ltl import (
    string_to_issy_ltl,
    unary_LTL_operators,
    binary_LTL_operators,
)

name_regex = r"(?!(true|false|sys( |\()|if ))[_a-zA-Z][_a-zA-Z0-9$@\_\-]*"
name = regex(name_regex)
state = regex(r"[a-zA-Z0-9@$_-]+")

regex_keywords = list(
    map(
        re.compile,
        [
            r"turn$",
            r"in_loop[0-9]+_[0-9]+",
            r"prog$",
            r"cs$",
            r"pred_.*",
            r"bin_.*",
            r"mismatch$",
            r"compatible_.*",
            r"guard_.*",
            r"act_.*",
            r"identity_.*",
            r"counterstrategy_guard_.*",
            r"counterstrategy_act_.*",
            r"floor$",
        ],
    )
)
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


def not_a_keyword(s: str):
    for k in list(regex_keywords):
        if k.match(s):
            raise Exception(
                "'"
                + s
                + "'"
                + " matches a reserved keyword/pattern "
                + str(k).replace("re.compile", "")
                + ", rename."
            )


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

    match op:
        case "and":
            return conjunct_formula_set(exprs)
        case "or":
            return disjunct_formula_set(exprs)
        case _:
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
    return process(name_str, vars_or_macros, objectives, games)


def process(name_str, vars_or_macros, objectives, games) -> tuple[Program, Formula]:
    con_vars = set()
    transitions = []

    if len(games) == 0:
        raise Exception("We do not handle yet ISSY problems with no games.")

    # process vars
    # build symbol table
    # separate inputs and state vars
    inputs = []
    state_vars = []
    next_state_vars = []
    macros = [v for v in vars_or_macros if len(v) == 2]

    macros = {Variable(k): v for k, v in macros}

    objectives = list(map(lambda a: a.replace_formulas(macros), objectives))
    for a in objectives:
        if any(v for v in a.variablesin() if v.is_next()):
            raise Exception(
                "We do not yet handle objectives with next-state variables: " + str(a)
            )

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

    game_parts = independent_games(inputs + state_vars, games)

    parts_to_sub_programs = []
    for i, game_part in enumerate(game_parts):
        if len(game_part) > 1:
            raise NotImplementedError(
                "Handling multiple dependent games is not supported yet."
            )
        vars_updated_in_game = set()
        vars_updates_depend_on_in_game = set()
        new_transitions = []
        game = game_part[0]
        game_type, init, locs_in_game, transitions = game

        marked_states = {}
        locs = []
        for v, kind, type in locs_in_game:
            locs.append(v.name)
            if type in marked_states.keys():
                marked_states[type].append(v)
            else:
                marked_states[type] = [v]

        updated_state_vars = {
            v for _, f, _ in transitions for v in f.variablesin() if v.is_next()
        }
        raw_transitions = {src: [] for src, _, _ in transitions}
        for src, formula, tgt in transitions:
            cond_updates = formula_to_transitions(
                formula, updated_state_vars, symbol_table
            )

            for cond, raw_updates in cond_updates:
                updates = []
                for raw_update in raw_updates:
                    f = strip_mathexpr(raw_update)
                    if isinstance(f, BiOp) and f.op == "=":
                        # TODO: normalise to prime variables on left and others on right
                        left, right = f.left, f.right
                        if isinstance(left, Variable) and left.is_next():
                            updates.append(create_update(left.prev_rep(), right))
                            vars_updated_in_game.add(left.prev_rep())
                            vars_updates_depend_on_in_game.update(right.variablesin())
                        else:
                            raise Exception(
                                "Update formula must be of the form x' = f: "
                                + str(raw_update)
                            )
                    else:
                        raise Exception(
                            "Update formula must be of the form x' = f: "
                            + str(raw_update)
                        )

                # Before adding, need to resolve determinism in transitions in favour of controller
                # Maybe, this should be a feature added at program level? Would also need to allow updates at LTL level
                # So that LTLMT formulas can be replaced appropriately
                # Would prevent replication of this logic in multiple parsers
                # For now we do it here

                raw_transitions[src].append(
                    Transition(
                        src,
                        cond,
                        updates,
                        [],
                        tgt,
                    )
                )

        new_transitions = []
        # need to detect when transitions from same src have non-mutually exclusive conditions, and in that case
        # create binary variables to distinguish them, and give them to controller
        for src, trans in raw_transitions.items():
            transition_partitioning = condition_choices(trans, symbol_table)
            if len(transition_partitioning) == 1:
                new_transitions.extend(transition_partitioning[0])
            else:
                raw_con_triggers = [
                    Variable("con_" + str(no))
                    for no in range(0, len(transition_partitioning))
                ]
                con_events, binary_map = binary_rep(
                    raw_con_triggers,
                    "con_",
                    printing=False,
                )
                con_vars.update(con_events)

                partition_conds = {
                    j: disjunct_formula_set([t.condition])
                    for j, p in enumerate(transition_partitioning)
                    for t in p
                }

                for k, part in enumerate(transition_partitioning):
                    one_of_the_rest = disjunct_formula_set(
                        [cond for n, cond in partition_conds.items() if k != n]
                    )
                    none_of_the_rest = neg(one_of_the_rest)
                    trigger: Formula = binary_map[raw_con_triggers[k]]
                    trigger_condition = disjunct(
                        none_of_the_rest, conjunct(one_of_the_rest, trigger)
                    )
                    for t in part:
                        new_transitions.append(
                            Transition(
                                t.src,
                                conjunct(t.condition, trigger_condition),
                                t.action,
                                [],
                                t.tgt,
                            )
                        )

        vars_updates_depend_on_in_game = vars_updates_depend_on_in_game.intersection(
            state_vars
        )
        if any(
            v for v in vars_updates_depend_on_in_game if v not in vars_updated_in_game
        ):
            raise NotImplementedError(
                "Handling of transitions where updates depend on variables not updated in the same game is not supported yet."
            )
        # build program for this game
        # need to massage vars according to expected format
        program = Program(
            name_str + "_part_" + str(i),
            locs,
            init,
            [(str(v), symbol_table[str(v)]) for v in vars_updated_in_game],
            new_transitions,
            [(v, symbol_table[str(v)]) for v in inputs],
            [(v, BOOLEAN) for v in con_vars],
        )

        match game_type:
            case "Buechi":
                objective_states = disjunct_formula_set(marked_states[1])
                objective = G(F(objective_states))
            case "Safety":
                objective_states = disjunct_formula_set(marked_states[1])
                objective = G(objective_states)
            case "Reachability":
                objective_states = disjunct_formula_set(marked_states[1])
                objective = F(objective_states)
            case "ParityMaxOdd":
                objective = parity_objective(marked_states)
            case _:
                raise Exception("Unknown game type: " + str(game_type))

        # if there are multiple games in a part, here need to add the cross product of transitions (and combine objectives)
        parts_to_sub_programs.append(
            (
                program,
                objective,
            )
        )

    # when len(parts_to_sub_programs) > 1, we either:
    #   1. perform cross-product of games (and combine objectives)
    #   2. perform interleaving of games (and modify objective accordingly)
    # For now we perform cross-product of games
    #   1. Create program for each game
    #   2. Create cross-product of programs
    #   3. Figure out objective for combined program
    if len(parts_to_sub_programs) == 1:
        new_obj = implies(conjunct_formula_set(objectives), parts_to_sub_programs[0][1])
        print(parts_to_sub_programs[0][0].to_prog(new_obj))
        return parts_to_sub_programs[0]
    else:
        new_prog, prog_old_to_new_state = program_cross_product(
            [p for p, _ in parts_to_sub_programs], symbol_table, name_str
        )
        new_objective = implies(
            conjunct_formula_set(objectives),
            conjunct_formula_set(
                [
                    obj.replace(
                        {
                            s: disjunct_formula_set(new_ss)
                            for s, new_ss in prog_old_to_new_state[i].items()
                        }
                    )
                    for i, (_, obj) in enumerate(parts_to_sub_programs)
                ]
            ),
        )
        print(new_prog.to_prog(new_objective))
        return new_prog, new_objective


def condition_choices(
    transitions: List[Transition], symbol_table
) -> List[List[Transition]]:
    # given a set of transitions
    # return a set of a set of transitions TS
    # such that for each Ts1, Ts2 in TS, and for each t1 in Ts1 and t2 in Ts2 then t1.condition and t2.condition are mutually exclusive
    # and each Ts1 and Ts2 do not intersect, and Ts1 union Ts2 ... union TsN = transitions

    if len(transitions) <= 1:
        return [transitions]
    combined_choices = []
    for i in range(0, len(transitions)):
        current_transition = transitions[i]
        current_cond = current_transition.condition
        added = False
        for choice in combined_choices:
            is_exclusive = True
            for existing_transition in choice:
                existing_cond = existing_transition.condition
                sat_formula = conjunct(current_cond, existing_cond)
                if sat(sat_formula, symbol_table):
                    is_exclusive = False
                    break
            if is_exclusive:
                choice.append(current_transition)
                added = True
                break
        if not added:
            combined_choices.append([current_transition])
    return combined_choices


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


def maximal_satisfiable_update_sets(updates, symbol_table):
    if not updates:
        return []

    indices = list(range(len(updates)))
    maximal = []

    for r in range(1, len(indices) + 1):
        for subset in itertools.combinations(indices, r):
            subset_updates = [updates[i] for i in subset]
            combined_update = conjunct_formula_set(subset_updates)
            if not sat(combined_update, symbol_table):
                continue

            subset_set = set(subset)
            dominated = False
            to_remove = []
            for existing in maximal:
                if subset_set.issubset(existing):
                    dominated = True
                    break
                if existing.issubset(subset_set):
                    to_remove.append(existing)

            if dominated:
                continue
            for existing in to_remove:
                maximal.remove(existing)
            maximal.append(subset_set)

    return [[updates[i] for i in sorted(subset)] for subset in maximal]


def formula_to_transitions(formula, state_vars, symbol_table):
    # TODO if already in dnf form, then just extract normally
    #   else the below
    preds = atomic_predicates(formula)
    updates = {f for f in preds if any(v for v in f.variablesin() if v.is_next())}
    if len(updates) != len(state_vars):
        raise Exception(
            "We do not handle unbounded next-state updates in formula: " + str(formula)
        )

    update_list = list(updates)
    update_combinations = maximal_satisfiable_update_sets(update_list, symbol_table)

    trans = []
    for combination in update_combinations:
        new_f = formula.replace_formulas(
            {u: false() for u in update_list if u not in combination}
        ).replace_formulas({u: true() for u in combination})
        dnfed_new_f = dnf(new_f, symbol_table)
        trans.append((dnfed_new_f, combination))

    return trans
