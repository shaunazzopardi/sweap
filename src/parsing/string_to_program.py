from multiprocessing import Pool

import parsec
from parsec import generate, string, sepBy, spaces, regex

import config
from parsing.keywords import is_keyword
from parsing.string_to_ltl import (
    string_to_ltl_with_predicates,
    string_to_program_action_formula,
)
from parsing.string_to_ltlmt import massage_ltl
from parsing.string_to_prop_logic import (
    string_to_math_expression,
    string_to_prop,
    string_to_negated_atom,
)
from parsing.util.game_transition_utils import (
    _resolve_nondeterminism,
    formula_to_transitions,
)
from programs.program import (
    Program,
    fill_in_minigames,
    materialize_otherwise_transitions,
)
from programs.transition import Transition
from programs.util import (
    guarded_action_transitions_to_normal_transitions,
    except_with_non_det_trans,
)
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import number_regex, BOOLEAN, parse_type, bool_regex
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.uniop import UniOp
from prop_lang.util import (
    true,
    normalize_ltl,
    conjunct,
    disjunct_formula_set,
    neg,
    sat,
    rewrite_boolean_equalities_as_iff,
    strip_mathexpr,
    G,
    F,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

name_regex = r"[_a-zA-Z][_a-zA-Z0-9$@\_\-]*"
name = regex(name_regex)
state = regex(r"[a-zA-Z0-9@$_-]+")


@generate
def program_parser():
    yield spaces() << regex("(program)|(arena)") >> spaces()
    program_name = yield name << spaces()
    yield string("{") >> spaces()
    sections = yield parsec.many(spaces() >> program_section_parser << spaces())
    yield spaces() >> string("}") >> spaces()

    section_values = {}
    for section_name, section_value in sections:
        if section_name in section_values:
            raise Exception(f"Duplicate section {section_name}.")
        section_values[section_name] = section_value

    required_sections = {"states", "env", "con", "initial_vals", "transitions"}
    missing = sorted(required_sections - set(section_values.keys()))
    if missing:
        raise Exception("Missing required section(s): " + ", ".join(missing))

    (states, initial_state) = section_values["states"]
    env = section_values["env"]
    con = section_values["con"]
    initial_vals = section_values["initial_vals"]
    semantics, completion, transitions = section_values["transitions"]
    ltl_spec = section_values.get("ltl_spec")

    program_var_names = {v[0] for v in initial_vals}
    in_out_var_names = {ev.name for ev, _ in env + con}
    for t in transitions:
        if isinstance(t.action, Formula):
            _validate_program_action_formula_vars(
                t.action,
                program_var_names,
                in_out_var_names,
            )

    state_vars = [Variable(v[0]) for v in initial_vals]
    if len(set(env + con + states + state_vars)) < len(env + con + states + state_vars):
        raise Exception(
            "Duplicate var names: "
            + ", ".join(
                [
                    str(v)
                    for v in env + con + states + state_vars
                    if (env + con + states + state_vars).count(v) > 1
                ]
            )
        )

    symbol_table = {v[0]: v[1] for v in initial_vals}
    guard_symbol_table = dict(symbol_table)
    guard_symbol_table.update({ev.name: t for ev, t in env + con})
    transitions = [
        t.with_condition(
            rewrite_boolean_equalities_as_iff(t.condition, guard_symbol_table)
        )
        for t in transitions
    ]
    otherwise_symbol_table = dict(guard_symbol_table)
    otherwise_symbol_table.update({state_name: BOOLEAN for state_name in states})
    transitions = materialize_otherwise_transitions(transitions, otherwise_symbol_table)

    transition_groups = [None] * len(transitions)
    guarded_action_args = []
    guarded_action_indices = []

    had_complex_action = False
    for i, t in enumerate(transitions):
        if isinstance(t.action, Formula):
            had_complex_action = True
            t.pred_upgrades = t.action
            t.action = []
            transition_groups[i] = [t]
        else:
            guarded_action_indices.append(i)
            guarded_action_args.append((t, initial_vals, env, con, symbol_table))

    if len(guarded_action_args) > 0:
        with Pool(config.Config.getConfig().workers) as pool:
            results = pool.map(
                guarded_action_transitions_to_normal_transitions, guarded_action_args
            )
        for i, result in zip(guarded_action_indices, results):
            transition_groups[i] = result

    new_transitions = [t for group in transition_groups for t in group]

    if semantics == "by-order":
        new_transitions = apply_transition_semantics_by_order(
            new_transitions, guard_symbol_table
        )

    states_for_program = list(states)
    if any(str(s) == "lose" for t in new_transitions for s in (t.src, t.tgt)):
        states_for_program.append("lose")

    program = Program(
        program_name,
        states_for_program,
        initial_state,
        initial_vals,
        new_transitions,
        env,
        con,
        transition_completion=completion,
    )

    if not program.deterministic:
        print(str(program))
        except_with_non_det_trans(program)

    if not had_complex_action and getattr(
        program, "added_completion_lose_transitions", False
    ):
        ltl_spec = conjunct(ltl_spec, G(neg(Variable("lose"))))
    if had_complex_action:
        new_transitions = []
        for t in program.transitions:
            new_transitions.extend(
                lower_program_action_formula_transition(t, initial_vals)
            )
        program = Program(
            program_name,
            states_for_program,
            initial_state,
            initial_vals,
            new_transitions,
            env,
            con,
            transition_completion=completion,
        )
        program, ltl_spec = postprocess_complex_action_program(program, ltl_spec)
    ltl_spec = ltl_spec.replace_formulas(
        {Variable(s): Value(BoolAtoms.FALSE) for s in states if s not in program.states}
    )
    print(program.to_prog(ltl_spec))
    return program, ltl_spec


@generate
def program_section_parser():
    return (
        yield parsec.try_choices(
            states_section_parser,
            env_section_parser,
            con_section_parser,
            initial_vals_section_parser,
            transitions_section_parser,
            spec_section_parser,
        )
    )


@generate
def states_section_parser():
    states = yield state_parser
    return "states", states


@generate
def env_section_parser():
    env = yield regex("(ENVIRONMENT EVENTS)|(INPUTS)") >> typed_event_parser
    return "env", env


@generate
def con_section_parser():
    con = yield regex("(CONTROLLER EVENTS)|(OUTPUTS)") >> typed_event_parser
    return "con", con


@generate
def initial_vals_section_parser():
    initial_vals = yield initial_val_parser
    return "initial_vals", initial_vals


@generate
def transitions_section_parser():
    transitions = yield transitions_parser(None)
    return "transitions", transitions


@generate
def spec_section_parser():
    ltl_spec = yield specification_parser
    return "ltl_spec", ltl_spec


def apply_transition_semantics_by_order(
    transitions: list[Transition], symbol_table
) -> list[Transition]:
    """Make transition guards source-local and priority-ordered.

    For each source state, transition i is rewritten to:
      guard_i & !(guard_1 | ... | guard_{i-1})
    preserving the input transition order.
    """
    covered_by_src = {}
    rewritten = []

    for t in transitions:
        covered = covered_by_src.get(t.src)
        effective_guard = (
            t.condition if covered is None else conjunct(t.condition, neg(covered))
        )
        covered_by_src[t.src] = (
            t.condition
            if covered is None
            else disjunct_formula_set([covered, t.condition])
        )

        if sat(effective_guard, symbol_table):
            rewritten.append(
                Transition(t.src, effective_guard, t.action, t.output, t.tgt)
            )

    return rewritten


@generate
def typed_event_parser():
    yield spaces() >> string("{") >> spaces()
    events = yield sepBy(
        parsec.try_choice(
            var_num_type_parser,
            parsec.try_choice(var_bool_type_parser, var_implicit_bool_type_parser),
        ),
        regex("(,|;)") << spaces(),
    )
    yield parsec.optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    return [(Variable(var), type) for var, type in events]


@generate
def var_implicit_bool_type_parser():
    var = yield name << spaces()
    return var, BOOLEAN


@generate
def state_parser():
    yield regex("(STATES)|(CONTROL STATES)") >> spaces() >> string("{") >> spaces()
    tagged_states = yield sepBy(
        tagged_state_parser << spaces(), regex("(,|;)") << spaces()
    )
    yield parsec.optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    initial_states = []
    for s, tag in tagged_states:
        is_keyword(s)
        if tag == "init":
            initial_states.append(s)
        elif tag != "":
            raise Exception("State tag " + tag + " is unknown.")
    if len(initial_states) != 1:
        raise Exception("Only one initial state allowed.")
    states = [s for (s, _) in tagged_states]
    return states, initial_states[0]


@generate
def tagged_state_parser():
    state_name = yield state << spaces()
    state_label = yield parsec.optional(
        string(":") >> spaces() >> regex("(init|flag)"), ""
    )
    return state_name, state_label


@generate
def var_bool_type_parser():
    var = yield name << spaces() << string(":") << spaces()
    yield regex(bool_regex) << spaces()
    return var, BOOLEAN


@generate
def bool_decl_parser():
    var, type = yield var_bool_type_parser
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;}]+") << spaces()
    try:
        value = string_to_prop(raw_value)
        return var, type, value
    except Exception as e:
        yield parsec.fail_with(str(e))


@generate
def var_num_type_parser():
    var = yield name << spaces() << string(":") << spaces()
    raw_type = yield regex(number_regex) << spaces()
    try:
        type = parse_type(raw_type)
        return var, type
    except Exception as e:
        yield parsec.fail_with(str(e))


@generate
def num_decl_parser():
    var = yield name << spaces() << string(":") << spaces()
    raw_type = yield regex(number_regex) << spaces()
    try:
        type = parse_type(raw_type)
    except Exception as e:
        yield parsec.fail_with(str(e))
    yield spaces()
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;}]+") << spaces()
    if raw_value == "*":
        return var, type, NonDeterministic()
    else:
        try:
            value = string_to_math_expression(raw_value)
            return var, type, value
        except Exception as e:
            yield parsec.fail_with(str(e))


@generate
def bool_decl_parser_untyped():
    var = yield name << spaces() << spaces()
    yield string(":=") << spaces()
    raw_value = yield regex(r"[^,;\]#]+") << spaces()
    action_and_guard = raw_value.split(" if ")
    try:
        if len(action_and_guard) == 1:
            value = string_to_prop(action_and_guard[0])
            guard = true()
        else:
            value = string_to_prop(action_and_guard[0])
            guard = string_to_prop(action_and_guard[1])
        return Update(Variable(var), value), guard
    except Exception as e:
        yield parsec.fail_with(str(e))


@generate
def num_decl_parser_untyped():
    var = yield name << spaces()
    yield string(":=") << spaces()
    raw_value = yield regex(r"[^,;\]#]+") << spaces()
    action_and_guard = raw_value.split(" if ")
    try:
        if len(action_and_guard) == 1:
            value = string_to_math_expression(action_and_guard[0])
            guard = true()
            return Update(Variable(var), value), guard
        else:
            value = string_to_math_expression(action_and_guard[0])
            guard = string_to_prop(action_and_guard[1])
            return Update(Variable(var), value), guard
    except Exception as e:
        yield parsec.fail_with(str(e))


@generate
def action_guard():
    yield string("if") << spaces() << spaces()
    raw_value = yield regex(r"[^,;\]#]+") << spaces()
    try:
        value = string_to_prop(raw_value)
        return value
    except Exception as e:
        yield parsec.fail_with(str(e))


@generate
def initial_val_parser():
    yield regex("(VALUATION)|(STATE VARIABLES)") >> spaces() >> string("{") >> spaces()
    vals = yield sepBy(
        parsec.try_choices(
            bool_decl_parser, num_decl_parser, var_bool_type_parser, var_num_type_parser
        ),
        regex("(,|;)") << spaces(),
    )
    yield spaces()
    yield parsec.optional(regex("(,|;)"))
    yield spaces() >> string("}")
    names = {v[0] for v in vals}
    list(map(is_keyword, names))
    if len(names) < len(vals):
        raise Exception("Variables with same name in VALUATION.")
    return vals


def transition_parser(program_var_names: set[str] | None = None):
    @generate
    def _transition_parser():
        yield spaces()
        source = yield state << spaces()
        yield regex("-+>") >> spaces()
        dest = yield state << spaces()
        yield string("[") >> spaces()
        raw_cond = yield parsec.optional(spaces() >> regex(r"[^$#\]]+"), "true")
        if raw_cond == "otherwise":
            cond = raw_cond
        else:
            cond = string_to_prop(raw_cond)
        yield spaces()
        act = yield parsec.optional(
            parsec.try_choice(
                make_transition_normal_action_parser(),
                make_transition_special_action_parser(program_var_names),
            )
            << spaces()
            << parsec.optional(regex("(,|;)") >> spaces())
            << parsec.lookahead(parsec.try_choice(string(">>"), string("]"))),
            [],
        )
        yield spaces()
        raw_events = yield parsec.optional(outputs, [])
        events = [string_to_negated_atom(e) for e in raw_events]
        yield spaces()
        yield string("]") >> spaces()
        if not cond:
            cond = true()
        return Transition(source, cond, act, events, dest)

    return _transition_parser


@generate
def outputs():
    outputs = (
        yield string(">>")
        >> spaces()
        >> sepBy(
            parsec.try_choice(bool_decl_parser_untyped, regex(r"[^\],;]+")) << spaces(),
            regex("(,|;)") >> spaces(),
        )
    )

    if len(
        {str(v.left) for v in outputs if isinstance(v, BiOp)}
        | {str(v) for v in outputs if not isinstance(v, BiOp)}
    ) < len(outputs):
        raise Exception("Output variables can only be assigned once by a transition.")
    return outputs


@generate
def assignments():
    assignment_and_guards = yield parsec.sepBy(
        parsec.try_choice(bool_decl_parser_untyped, num_decl_parser_untyped),
        regex("(,|;)") >> spaces(),
    ) << parsec.optional(regex("(,|;)") >> spaces())
    return assignment_and_guards


def _validate_program_action_formula_vars(
    formula: Formula,
    program_var_names: set[str] | None,
    in_out_now_var_names: set[str] | None = None,
) -> None:
    if program_var_names is None:
        return
    if in_out_now_var_names is None:
        in_out_now_var_names = set()

    invalid_next = set()
    invalid_now = set()
    for v in formula.variablesin():
        if not isinstance(v, Variable):
            continue
        if v.is_next():
            if str(v.prev_rep()) not in program_var_names:
                invalid_next.add(str(v))
            continue
        if str(v) not in program_var_names and str(v) not in in_out_now_var_names:
            invalid_now.add(str(v))

    if invalid_next or invalid_now:
        invalid = sorted(invalid_next | invalid_now)
        raise Exception(
            "Program action formula may only reference local state variables (now/next) "
            "and input/output variables (now only): " + ", ".join(invalid)
        )


def parse_program_action_formula_text(
    text: str,
    program_var_names: set[str] | None = None,
    in_out_now_var_names: set[str] | None = None,
) -> Formula:
    stripped = text.strip()
    formula = true() if stripped == "" else string_to_program_action_formula(stripped)
    _validate_program_action_formula_vars(
        formula,
        program_var_names,
        in_out_now_var_names,
    )
    return formula


def make_program_action_formula_parser(
    program_var_names: set[str] | None = None,
    in_out_now_var_names: set[str] | None = None,
):
    @generate
    def program_action_formula_parser():
        raw_value = yield parsec.optional(regex(r"(?s)(?:(?!>>|\]).)+"), "")
        yield spaces()
        try:
            return parse_program_action_formula_text(
                raw_value,
                program_var_names,
                in_out_now_var_names,
            )
        except Exception as e:
            yield parsec.fail_with(str(e))

    return program_action_formula_parser


def make_transition_normal_action_parser():
    @generate
    def transition_normal_action_parser():
        yield string("$") >> spaces()
        empty_body = yield parsec.optional(
            parsec.lookahead(string("]")),
            None,
        )
        if empty_body is not None:
            return []
        raw_value = yield parsec.optional(regex(r"(?s)(?:(?!\]).)+"), "")
        try:
            actions = (assignments << parsec.eof()).parse(
                raw_value.strip().rstrip(",;")
            )
            updated_vars = {}
            for act in actions:
                if not isinstance(act[1], Value):
                    continue
                if act[0].left in updated_vars.keys():
                    e = (
                        "Variable "
                        + str(act[0].left)
                        + " assigned multiple times: "
                        + str(updated_vars[act[0].left])
                        + " and "
                        + str(act[0])
                    )
                    print(e)
                    yield parsec.fail_with(e)
                else:
                    updated_vars[act[0].left] = act[0]
            return actions
        except Exception as e:
            yield parsec.fail_with(str(e))

    return transition_normal_action_parser


def make_transition_special_action_parser(
    program_var_names: set[str] | None = None,
    in_out_now_var_names: set[str] | None = None,
):
    @generate
    def transition_special_action_parser():
        yield string("#") >> spaces()
        empty_body = yield parsec.optional(
            parsec.lookahead(parsec.try_choice(string(">>"), string("]"))),
            None,
        )
        if empty_body is not None:
            return parse_program_action_formula_text(
                "",
                program_var_names,
                in_out_now_var_names,
            )
        formula = yield make_program_action_formula_parser(
            program_var_names,
            in_out_now_var_names,
        )
        yield spaces()
        yield parsec.optional(regex("(,|;)") >> spaces())
        yield parsec.lookahead(parsec.try_choice(string(">>"), string("]")))
        return formula

    return transition_special_action_parser


def _program_action_symbol_table(
    initial_vals: list[tuple[str, object] | tuple[str, object, object]],
) -> dict[str, object]:
    symbol_table = {}
    for v in initial_vals:
        symbol_table[v[0]] = v[1]
        symbol_table[v[0] + "'"] = v[1]
    return symbol_table


def lower_program_action_formula_transition(
    transition: Transition,
    initial_vals: list[tuple[str, object] | tuple[str, object, object]],
) -> list[Transition]:
    if not isinstance(transition.pred_upgrades, Formula):
        return [transition]

    symbol_table = _program_action_symbol_table(initial_vals)
    program_vars = {Variable(v[0]) for v in initial_vals}
    cond_updates = formula_to_transitions(
        strip_mathexpr(transition.pred_upgrades), [], symbol_table
    )
    covered_conditions = [cond for cond, _ in cond_updates]

    lowered = []
    for cond, raw_update_sets in cond_updates:
        for raw_updates in raw_update_sets:
            predicate_upgrades = []
            updates = []
            for raw_update in raw_updates:
                f = strip_mathexpr(raw_update)
                if isinstance(f, Variable) and f.is_next():
                    updates.append(Update(f.prev_rep(), true()))
                    continue
                if (
                    isinstance(f, UniOp)
                    and f.op == "!"
                    and isinstance(f.right, Variable)
                    and f.right.is_next()
                ):
                    updates.append(Update(f.right.prev_rep(), Value(BoolAtoms.FALSE)))
                    continue

                if isinstance(f, BiOp) and f.op == "=":
                    left, right = f.left, f.right
                    if (
                        isinstance(left, Variable)
                        and left.is_next()
                        and not any(v for v in right.variablesin() if v.is_next())
                    ):
                        updates.append(Update(left.prev_rep(), right))
                        continue

                    if (
                        isinstance(right, Variable)
                        and right.is_next()
                        and not any(v for v in left.variablesin() if v.is_next())
                    ):
                        updates.append(Update(right.prev_rep(), left))
                        continue

                predicate_upgrades.append(raw_update)

            vars_updated_in_transition = {u.left for u in updates}
            vars_not_updated = program_vars - vars_updated_in_transition
            for v in sorted(vars_not_updated, key=str):
                updates.append(Update(v, NonDeterministic()))

            lowered_transition = Transition(
                transition.src,
                conjunct(transition.condition, cond),
                updates,
                transition.output,
                transition.tgt,
            )
            lowered_transition.set_predicate_upgrades(predicate_upgrades)
            lowered.append(lowered_transition)

    return lowered


def postprocess_complex_action_program(
    program: Program, ltl_spec: Formula
) -> tuple[Program, Formula]:
    to_exclude_from_minigame = []
    lose_var = None

    if not program.deterministic:
        program, lose_var, to_exclude_from_minigame = _resolve_nondeterminism(
            program,
            dict(program.symbol_table),
            list(to_exclude_from_minigame),
        )

    has_pred_upgrades = any(len(t.pred_upgrades) > 0 for t in program.orig_ts)
    minigame_states = []
    if has_pred_upgrades:
        program, minigame_states = fill_in_minigames(
            program,
            [ltl_spec],
            to_exclude_from_minigame,
        )

    if len(minigame_states) > 0:
        not_in_minigame = neg(disjunct_formula_set(minigame_states))
        ltl_spec = massage_ltl(ltl_spec, not_in_minigame, {})
        ltl_spec = conjunct(
            ltl_spec,
            G(F(neg(disjunct_formula_set(minigame_states)))),
        )

    effective_lose_var = (
        lose_var
        if lose_var is not None
        else ("lose" if "lose" in program.states else None)
    )
    if effective_lose_var is not None:
        ltl_spec = conjunct(ltl_spec, G(neg(Variable(effective_lose_var))))

    return program, normalize_ltl(ltl_spec)


make_transition_action_formula_parser = make_transition_special_action_parser


@generate
def nondet_assignment():
    yield string("*") << spaces()
    yield string("[") << spaces()
    raw_value = yield regex("[^\\]]+") << spaces()
    yield string("]") << spaces()
    condition = string_to_prop(raw_value)
    # doesn t handle nexts
    return condition


def transitions_parser(program_var_names: set[str] | None = None):
    @generate
    def _transitions_parser():
        yield string("TRANSITIONS") >> spaces()
        semantics = ""
        completion = ""
        raw_options = yield parsec.optional(
            string("[") >> spaces() >> regex(r"[^\]]*") << spaces() << string("]"),
            None,
        )
        if raw_options is not None:
            options = [
                option.strip()
                for option in raw_options.replace(";", ",").split(",")
                if option.strip()
            ]
            for option in options:
                key, sep, value = option.partition("=")
                if sep == "":
                    raise ValueError(f"Invalid transition option: {option}")
                key = key.strip()
                value = value.strip()
                if key == "semantics":
                    if value != "by-order":
                        raise ValueError(f"Unsupported transition semantics: {value}")
                    semantics = value
                elif key == "completion":
                    if value not in {"stutter", "lose"}:
                        raise ValueError(f"Unsupported transition completion: {value}")
                    completion = value
                else:
                    raise ValueError(f"Unknown transition option: {key}")
        yield spaces()
        yield string("{") >> spaces()
        transitions = yield sepBy(
            transition_parser(program_var_names),
            spaces() >> regex("(,|;)") >> spaces(),
        )
        yield spaces() >> parsec.optional(regex("(,|;)") >> spaces())
        yield spaces() >> string("}")
        return semantics, completion, transitions

    return _transitions_parser


@generate
def specification_parser():
    yield regex("(SPECIFICATION)|(OBJECTIVE)") >> spaces()
    yield string("{") >> spaces()
    ltl_spec_string = yield regex("[^}]*")
    yield spaces() >> string("}")
    ltl_spec = string_to_ltl_with_predicates(ltl_spec_string)
    ltl_spec = normalize_ltl(ltl_spec)
    return ltl_spec


parser = program_parser


def string_to_program(input: str) -> tuple[Program, Formula]:
    program, ltl_spec = (parser << parsec.eof()).parse(input)
    return program, ltl_spec
