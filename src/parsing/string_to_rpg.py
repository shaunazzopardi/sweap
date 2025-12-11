import re

import parsec
from parsec import generate, string, sepBy, spaces, regex, many1

import config
from programs.program import Program
from programs.transition import Transition
from programs.util import binary_rep
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
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import (
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
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.machines.wrapped_hoa import WrappedHOA
from synthesis.synthesis import synthesize

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
        not_a_keyword(str(v))
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

    new_init, env_vars, con_vars, new_states, transitions = process(
        inputs,
        vars,
        init,
        transitions,
    )

    non_bool_inputs = {v: t for v, t in inputs.items() if t != BOOLEAN}
    program = Program(
        config.Config.getConfig().name,
        list(states) + new_states,
        new_init,
        [(str(v), t, init_values[t]) for v, t in (non_bool_inputs | vars).items()],
        transitions,
        list(env_vars),
        list(con_vars),
        preprocess=False,
    )
    input_toggle_states = disjunct_formula_set(map(lambda x: Variable(x), new_states))

    match game_type:
        case "Buechi":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = G(F(objective_states))
        case "Safety":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = G(disjunct(objective_states, input_toggle_states))
        case "Reach":
            objective_states = disjunct_formula_set(marked_states[1])
            objective = F(objective_states)
        case "Parity":
            objective = parity_objective(marked_states)
        case _:
            raise Exception("Unknown game type: " + str(game_type))

    if len(new_states) == 0:
        ltl_spec = objective
    else:
        ltl_spec = implies(
            G(F(neg(input_toggle_states))),
            objective,
        )
    return program, ltl_spec


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
        ret[frozenset([(frozenset([]), second)])] = neg(cond)
    elif isinstance(second, frozenset):
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
    v = yield (string("true") | string("false"))
    return create_value(v)


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


def rpg_parsec(input: str) -> tuple[Program, Formula]:
    input_wo_comments = re.sub(";[^\n]*(\n|$)", "", input)
    rpg, ltl = (parser << parsec.eof()).parse(input_wo_comments)
    return rpg, ltl


def process(inputs, state_vars, init, src_update_tuples):
    # TODO need to init initial values of variables
    new_init = init
    new_states = []
    new_tgts = {}
    new_transitions = []
    env_vars = set()
    con_vars = set()
    transitions = {}
    for src, rest in src_update_tuples:
        if src in transitions.keys():
            raise Exception("Multiple 'trans' from state " + src + "'.")

        transitions[src] = []
        if isinstance(rest, str):
            transitions[src].append(Transition(src, true(), [], [], rest))
        elif isinstance(rest, frozenset):
            if len(rest) == 1:
                u_tgt = list(rest)[0]
                transitions[src].append(
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
                transitions[src].append(Transition(src, binary_map[i], list(u), [], d))
        else:
            if len(rest) == 1:
                u_t, c = list(rest.items())[0]
                if len(u_t) == 1:
                    u = list(u_t)[0]
                    if isinstance(u, str):
                        transitions[src].append(Transition(src, c, [], [], u))
                    else:
                        transitions[src].append(
                            Transition(src, c, list(u[0]), [], u[1])
                        )
                    continue
            for us, c in rest.items():
                con_events, binary_map = binary_rep(
                    range(0, len(us)), "con_", printing=False
                )
                binary_map[len(us) - 1] = neg(
                    disjunct_formula_set(
                        binary_map[i] for i in range(0, len(us)) if i < len(us) - 1
                    )
                )
                # TODO consider trying to simplify this, with something of the for (bin_0 & (.. || ..)) || (!bin_0 & (.. || ..))
                #       this will be useful depending on what the underlying synthesis engine does
                con_vars.update(con_events)
                for i, u_tgt in enumerate(us):
                    if isinstance(u_tgt, str):
                        transitions[src].append(
                            Transition(src, conjunct(c, binary_map[i]), [], [], u_tgt)
                        )
                    else:
                        transitions[src].append(
                            Transition(
                                src,
                                conjunct(c, binary_map[i]),
                                list(u_tgt[0]),
                                [],
                                u_tgt[1],
                            )
                        )

    for src, ts in transitions.items():
        inputs_needed = {
            i
            for i in inputs.keys()
            for t in ts
            if i in t.condition.variablesin()
            or any(True for u in t.action if i in u.right.variablesin())
        }
        if len(inputs_needed) == 0:
            new_tgts[src] = src
            continue
        else:
            to_remove = set()
            for v in inputs_needed:
                if inputs[v] == BOOLEAN:
                    env_vars.add(v)
                    to_remove.add(v)
            inputs_needed -= to_remove
            if len(inputs_needed) == 0:
                continue

            new_e = "e_" + src
            new_states.append(new_e)
            new_tgts[src] = new_e
            if src == init:
                new_init = new_e

            orig_end_env = Variable("end")
            env_events, binary_map = binary_rep(
                inputs_needed | set(map(neg, inputs_needed)) | {orig_end_env},
                "env_",
                printing=False,
            )
            env_vars.update(env_events)
            env_t = []
            end_env = neg(
                disjunct_formula_set(
                    f for v, f in binary_map.items() if v != orig_end_env
                )
            )

            # TODO initially the environment can set the program vars to any value
            #       can assume stuff in assume to limit
            for v, f in binary_map.items():
                if v == orig_end_env:
                    env_t.append(
                        Transition(
                            new_e,
                            end_env,
                            [],
                            [],
                            src,
                        )
                    )
                elif isinstance(v, UniOp) and v.op == "!":
                    if inputs[v.right] == INTEGER:
                        env_t.append(
                            Transition(
                                new_e,
                                f,
                                [Update(v.right, BiOp(v.right, "-", Value("1")))],
                                [],
                                new_e,
                            )
                        )
                    else:
                        raise Exception(
                            "Unsupported type for variable "
                            + str(v)
                            + ": "
                            + str(inputs[v.right])
                        )
                else:
                    if inputs[v] == INTEGER:
                        env_t.append(
                            Transition(
                                new_e,
                                f,
                                [Update(v, BiOp(v, "+", Value("1")))],
                                [],
                                new_e,
                            )
                        )
                    else:
                        raise Exception(
                            "Unsupported type for variable "
                            + str(v)
                            + ": "
                            + str(inputs[v])
                        )

            new_transitions.extend(env_t)

    new_tgt = lambda t: new_tgts[t.tgt] if t.tgt in new_tgts.keys() else t.tgt
    new_transitions.extend(
        {t.to(new_tgt(t)) for _, ts in transitions.items() for t in ts}
    )

    if len(state_vars) > 0:
        # create fresh init state where env can set the program variables initial values
        fresh_init = "prog_vars_toggle"
        new_states.append(fresh_init)
        orig_end_env = Variable("end")
        env_events, binary_map = binary_rep(
            state_vars.keys() | set(map(neg, state_vars.keys())) | {orig_end_env},
            "env_",
            printing=False,
        )
        env_vars.update(env_events)
        end_env = neg(
            disjunct_formula_set(f for v, f in binary_map.items() if v != orig_end_env)
        )
        for v, f in binary_map.items():
            if v == orig_end_env:
                new_transitions.append(
                    Transition(
                        fresh_init,
                        end_env,
                        [],
                        [],
                        new_init,
                    )
                )
            elif isinstance(v, UniOp) and v.op == "!":
                if state_vars[v.right] == INTEGER:
                    new_transitions.append(
                        Transition(
                            fresh_init,
                            f,
                            [Update(v.right, BiOp(v.right, "-", Value("1")))],
                            [],
                            fresh_init,
                        )
                    )
                elif state_vars[v.right] == BOOLEAN:
                    new_transitions.append(
                        Transition(
                            fresh_init,
                            f,
                            [Update(v.right, Value(BoolAtoms.FALSE))],
                            [],
                            fresh_init,
                        )
                    )
                else:
                    raise Exception(
                        "Unsupported type for variable "
                        + str(v)
                        + ": "
                        + str(inputs[v.right])
                    )
            else:
                if state_vars[v] == INTEGER:
                    new_transitions.append(
                        Transition(
                            fresh_init,
                            f,
                            [Update(v, BiOp(v, "+", Value("1")))],
                            [],
                            fresh_init,
                        )
                    )
                elif state_vars[v] == BOOLEAN:
                    new_transitions.append(
                        Transition(
                            fresh_init,
                            f,
                            [Update(v, Value(BoolAtoms.TRUE))],
                            [],
                            fresh_init,
                        )
                    )
                else:
                    raise Exception(
                        "Unsupported type for variable "
                        + str(v)
                        + ": "
                        + str(inputs[v])
                    )
    else:
        fresh_init = new_init

    return fresh_init, env_vars, con_vars, new_states, new_transitions


def parity_objective(marked_states: dict[int, list[str]]) -> Formula:
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
