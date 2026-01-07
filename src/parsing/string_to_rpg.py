import logging
import re

import parsec
from parsec import choice, generate, string, sepBy, spaces, regex, many1

from parsing.keywords import is_keyword
from programs.program import Program
from programs.transition import Transition
from programs.util import binary_rep, refine_init_values
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
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.util import (
    true,
    neg,
    conjunct,
    disjunct_formula_set,
    simplify_formula_without_math,
    conjunct_formula_set,
    G,
    F,
    disjunct,
    sat,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

name_regex = r"(?!(true|false|sys( |\()|if ))[_a-zA-Z][_a-zA-Z0-9$@\_\-]*"
name = regex(name_regex)
state = regex(r"[a-zA-Z0-9@$_-]+")

math_ops = {"=", "!=", "<", "<=", ">", ">=", "+", "-"}

unary_operators = {"not": "!", "-": "-"}
binary_operators = {"=>": "->", "=": "->", "and": "&", "or": "|"}

types = {
    "Int": INTEGER,
    "Bool": BOOLEAN,
    # "Real": REAL,
    "BInt": INTEGER,
    # "BReal": REAL,
}

init_values = {
    INTEGER: Value("0"),
    BOOLEAN: Value(BoolAtoms.FALSE),
    # "real": Value("0.0"),
}


@generate
def rpg_parser():
    yield string("type") >> spaces()
    game_type = yield name << spaces()
    yield spaces()
    vs = yield many1((loc_parser | var_dec_parser) << spaces())
    yield spaces()
    init = yield string("init") >> spaces() >> name
    yield spaces()
    transitions = yield transitions_parser
    inputs = {}
    vars = {}
    states = set()
    marked_states = {}

    for v, kind, type in vs:
        is_keyword(str(v))
        if v in inputs.keys() or v in vars.keys() or v in states:
            raise Exception(v + "' defined multiple times.")

        match kind:
            case "input":
                inputs[v] = type
            case "output":
                vars[v] = type
            case "loc":
                states.add(v.name)
                if type in marked_states.keys():
                    marked_states[type].append(v)
                else:
                    marked_states[type] = [v]
            case _:
                raise Exception("Unknown var kind: " + str(kind))

    new_init, con_vars, transitions = process(
        inputs,
        vars,
        init,
        transitions,
    )

    program = Program(
        file_name,
        list(states),
        new_init,
        [(str(v), t) for v, t in vars.items()],
        transitions,
        list(inputs.items()),
        [(v, BOOLEAN) for v in con_vars],
        preprocess=False,
    )
    refine_init_values(program, true())

    marked_states = {
        k: [s for s in v if s.name in program.states] for k, v in marked_states.items()
    }

    match game_type:
        case "Buechi":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = G(F(objective_states))
        case "Safety":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = G(objective_states)
        case "Reach":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = F(objective_states)
        case "Parity":
            objective = parity_objective(marked_states)
        case _:
            raise Exception("Unknown game type: " + str(game_type))

    print(program.to_prog(objective))
    logging.info(program.to_prog(objective))
    return program, objective


@generate
def var_dec_parser():
    kind = yield string("input") | string("output")
    yield spaces()
    var = yield var_parser
    yield spaces()
    var_type = yield regex("(Bool|Int|BInt|Real|BReal)")
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
def update_parser():
    yield string("sys")
    yield spaces()
    yield string("(")
    yield spaces()
    updates = yield parsec.many(update_choice_parser << spaces())
    yield spaces()
    yield string(")")
    return frozenset(updates)


@generate
def update_choice_parser():
    yield string("(")
    yield spaces()
    updates = yield parsec.many(update_list_parser << spaces())
    yield spaces()
    yield string(")")
    yield spaces()
    dest = yield name
    yield spaces()
    return frozenset(updates), dest


@generate
def update_list_parser():
    yield string("(")
    var = yield var_parser
    yield spaces()
    update = yield expr_parser
    yield spaces()
    yield string(")")
    return create_update(var, update)


@generate
def ite_parser():
    yield string("if")
    yield spaces()
    cond = yield expr_parser
    yield spaces()
    yield string("then")
    yield spaces()
    first = yield update_parser ^ ite_parser ^ name
    yield spaces()
    yield string("else")
    yield spaces()
    second = yield update_parser ^ ite_parser ^ name

    if isinstance(first, str):
        ret = {(frozenset([(frozenset([]), first)])): cond}
    elif isinstance(first, frozenset):
        ret = {first: cond}
    else:
        ret = {u: conjunct(cond, c) for u, c in first.items()}

    if isinstance(second, str):
        new_second = frozenset([(frozenset([]), second)])
        if new_second in ret.keys():
            ret[new_second] = disjunct(ret[new_second], neg(cond))
        else:
            ret[new_second] = neg(cond)
    elif isinstance(second, frozenset):
        if second in ret.keys():
            ret[second] = disjunct(ret[second], neg(cond))
        else:
            ret[second] = neg(cond)
    else:
        for u, c in second.items():
            neg_cond = conjunct(neg(cond), c)
            if u in ret.keys():
                ret[u] = disjunct(neg_cond, ret[u])
            else:
                ret[u] = neg_cond
    return ret


@generate
def bi_expr_parser():
    yield string("(")
    yield spaces()
    op = yield regex("(>=|<=|>|<|!=|=|!|\\*)")
    yield spaces()
    first = yield expr_parser
    yield spaces()
    second = yield expr_parser
    yield spaces()
    yield string(")")
    yield spaces()

    return create_mathrel(first, op, second)


@generate
def x_expr_parser():
    yield string("(")
    yield spaces()
    op = yield regex("(\\+|-|and|or)")
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
    yield string("(")
    op = yield regex("(not|-)")
    yield spaces()
    first = yield expr_parser
    yield spaces()
    yield string(")")
    if op == "-":
        return create_neg_no(first)
    else:
        return create_uniop("!", first)


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
    return create_value(v)


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
def expr_parser():
    v = (
        yield var_parser
        ^ value_parser
        ^ uni_expr_parser
        ^ bi_expr_parser
        ^ x_expr_parser
        ^ (string("(") >> spaces() >> expr_parser << spaces() << string(")"))
    )
    return v


@generate
def transition_parser():
    yield spaces()
    yield string("trans")
    yield spaces()
    src = yield name
    yield spaces()
    rest = yield (ite_parser ^ update_parser ^ name)
    yield spaces()
    return src, rest


@generate
def basic_transition_parser():
    yield spaces()
    yield string("trans")
    yield spaces()
    src = yield name
    yield spaces()
    dest = yield name
    yield spaces()
    return src, dest


@generate
def transitions_parser():
    yield spaces()
    transitions = yield many1(parsec.choice(transition_parser, basic_transition_parser))
    yield spaces()
    return transitions


parser = rpg_parser


def rpg_parsec(input: str, name_str: str) -> tuple[Program, Formula]:
    input_wo_comments = re.sub(";[^\n]*(\n|$)", "", input)
    global file_name
    file_name = name_str
    rpg, ltl = (parser << parsec.eof()).parse(input_wo_comments)
    return rpg, ltl


def process(inputs, state_vars, init, src_update_tuples):
    con_vars = set()
    transitions = []
    symbol_table = {str(v): t for v, t in (inputs | state_vars).items()}
    seen_srcs = set()
    # TODO: when RPG transitions have same src, tgt, and guard, but different update choices
    #       the effects_abstraction should have transitions of the form:
    #       guard -> ((trigger1 and u_1) or ... (trigger2 and u_n))
    #       so abstraction becomes (now, list[(trigger, [nexts])])
    #       this will keep abstraction smaller
    for src, rest in src_update_tuples:
        if src in seen_srcs:
            raise Exception("Multiple 'trans' from state " + src + "'.")

        if isinstance(rest, str):
            transitions.append(Transition(src, true(), [], [], rest))
        elif isinstance(rest, frozenset):
            if len(rest) == 1:
                u_tgt = list(rest)[0]
                transitions.append(
                    Transition(src, true(), list(u_tgt[0]), [], u_tgt[1])
                )
                continue

            con_events, binary_map = binary_rep(
                range(0, len(rest)), "con_", printing=False
            )
            binary_map[len(rest) - 1] = neg(
                disjunct_formula_set(
                    binary_map[i] for i in range(0, len(rest)) if i < len(rest) - 1
                )
            )
            binary_map[len(rest) - 1] = simplify_formula_without_math(
                binary_map[len(rest) - 1]
            )
            con_vars.update(con_events)
            for i, (u, d) in enumerate(rest):
                transitions.append(Transition(src, binary_map[i], list(u), [], d))
        else:
            if len(rest) == 1:
                u_t, c = list(rest.items())[0]
                if len(u_t) == 1:
                    u = list(u_t)[0]
                    if isinstance(u, str):
                        transitions.append(Transition(src, c, [], [], u))
                    else:
                        transitions.append(Transition(src, c, list(u[0]), [], u[1]))
                    continue
            if conds_mutually_exclusive(list(rest.values()), symbol_table):
                left_to_do = {}
                for us, c in rest.items():
                    if len(us) != 1:
                        left_to_do[us] = c
                        continue
                    else:
                        for u_tgt in us:
                            if isinstance(u_tgt, str):
                                transitions.append(Transition(src, c, [], [], u_tgt))
                            else:
                                transitions.append(
                                    Transition(
                                        src,
                                        c,
                                        list(u_tgt[0]),
                                        [],
                                        u_tgt[1],
                                    )
                                )
                if len(left_to_do) == 0:
                    continue
                else:
                    rest = left_to_do
            for us, c in rest.items():
                con_events, binary_map = binary_rep(
                    range(0, len(us)), "con_", printing=False
                )
                binary_map[len(us) - 1] = neg(
                    disjunct_formula_set(
                        binary_map[i] for i in range(0, len(us)) if i < len(us) - 1
                    )
                )
                con_vars.update(con_events)
                for i, u_tgt in enumerate(us):
                    if isinstance(u_tgt, str):
                        transitions.append(
                            Transition(src, conjunct(c, binary_map[i]), [], [], u_tgt)
                        )
                    else:
                        transitions.append(
                            Transition(
                                src,
                                conjunct(c, binary_map[i]),
                                list(u_tgt[0]),
                                [],
                                u_tgt[1],
                            )
                        )

    return init, con_vars, transitions


def parity_objective(marked_states: dict[int, list[str]]) -> Formula:
    marked_states = {
        k + 1: v for k, v in marked_states.items()
    }  # make priorities 1-based
    parities = list(marked_states.keys())
    parities.sort()
    smallest_is_odd = parities[0] % 2 == 1

    if len(parities) == 1:
        if smallest_is_odd:
            raise Exception(
                "Parity objective with only one odd priority is unrealizable."
            )
        elif not smallest_is_odd:
            raise Exception(
                "Parity objective with only one even priority is trivially realizable."
            )

    even_to_larger_odds = {}

    for p in parities:
        if p % 2 == 0:
            even_to_larger_odds[p] = []
        else:
            for even in even_to_larger_odds.keys():
                even_to_larger_odds[even].extend(marked_states[p])

    if len(even_to_larger_odds.keys()) == 0:
        raise Exception("Parity objective with only odd priorities is unrealizable.")
    if len(even_to_larger_odds.keys()) == len(parities):
        raise Exception(
            "Parity objective with only even priorities is trivially realizable."
        )

    objectives = []

    for even, odds in even_to_larger_odds.items():
        even_states = disjunct_formula_set(marked_states[even])
        odd_states = disjunct_formula_set(odds)
        if len(odds) > 0:
            objectives.append(conjunct(G(F(even_states)), neg(G(F(odd_states)))))
        else:
            objectives.append(G(F(even_states)))

    return disjunct_formula_set(objectives)


def conds_mutually_exclusive(conds: list[Formula], symbol_table) -> bool:
    for i in range(0, len(conds)):
        for j in range(i + 1, len(conds)):
            sat_formula = conjunct(conds[i], conds[j])
            if sat(sat_formula, symbol_table):
                return False
    return True
