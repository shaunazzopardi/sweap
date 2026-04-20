from __future__ import annotations

import config
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, NATURAL, Number, countable_number_types
from prop_lang.util import X, conjunct_formula_set

from analysis.compatibility_checking.renderer import render_structured_model
from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl


def program_state_symbol_map(states) -> dict:
    ordered_states = sorted(list(states), key=str)
    return {st: f"program_q_{i}" for i, st in enumerate(ordered_states)}


def program_to_nuxmv_model(
    program: Program,
) -> StructuredNuXmvModel:
    state_var = "program_state"
    if state_var in set(program.local_vars_str):
        raise ValueError(
            "program variable name 'program_state' collides with tandem enum state variable"
        )

    real_acts = []
    guards = []
    acts = []
    dual = config.Config.getConfig().dual
    state_symbols = program_state_symbol_map(program.states)
    single_state = len(program.states) == 1
    only_state = sorted(list(program.states), key=str)[0] if single_state else None

    for transition in program.transitions:
        if dual:
            # In dual compatibility/verification tandem models, program guards
            # are evaluated on the current step (no automatic next-shift).
            cond = transition.condition.to_nuxmv()
        else:
            cond = transition.condition.to_nuxmv()

        state_guard = (
            "TRUE"
            if single_state
            else f"({state_var} = {state_symbols[transition.src]})"
        )
        guard = state_guard + " & (" + cond + ")"

        bare_acts = []
        for u in program.complete_action_set(transition.action):
            if dual:
                right = u.right
            else:
                right = u.right
            bare_acts.append(BiOp(X(u.left), "=", right))

        bare_acts_nuxmv = (
            conjunct_formula_set(bare_acts).to_nuxmv().replace("X(", "next(")
        )
        if single_state:
            act = f"({bare_acts_nuxmv})"
        else:
            act = (
                f"(next({state_var}) = {state_symbols[transition.tgt]})"
                f" & ({bare_acts_nuxmv})"
            )

        guards.append(guard)
        acts.append(act)
        real_acts.append((transition.action, transition.output, transition.tgt))

    real_acts.append(([], [], None))  # for stutter transition

    if single_state:
        define = [
            f"{st} := {'TRUE' if st == only_state else 'FALSE'}"
            for st in sorted(list(program.states), key=str)
        ]
    else:
        define = [
            f"{st} := ({state_var} = {state_symbols[st]})"
            for st in sorted(list(program.states), key=str)
        ]
    guard_and_act = []
    guard_ids = []
    for i in range(len(guards)):
        define.append("guard_" + str(i) + " := " + guards[i])
        define.append("act_" + str(i) + " := " + acts[i])
        guard_ids.append("guard_" + str(i))
        guard_and_act.append("(guard_" + str(i) + " & act_" + str(i) + ")")

    identity = []
    for var in program.local_vars_str:
        identity.append("next(" + var + ") = " + var)
    if not single_state:
        identity.append(f"next({state_var}) = {state_var}")
    identity += ["!next(" + str(event) + ")" for event in program.out_events]

    identity_macro_name = "identity_" + program.name
    define.append(identity_macro_name + " := " + " & ".join(identity))

    # if no guard holds, then keep the same state and output no program events
    guards.append("!(" + " | ".join(guard_ids) + ")")
    acts.append(identity_macro_name)
    define.append("guard_" + str(len(guards) - 1) + " := " + guards[len(guards) - 1])
    define.append("act_" + str(len(guards) - 1) + " := " + acts[len(guards) - 1])
    guard_and_act.append(
        "(guard_" + str(len(guards) - 1) + " & act_" + str(len(guards) - 1) + ")"
    )

    transitions = guard_and_act

    state_enum = ", ".join(
        state_symbols[s] for s in sorted(list(program.states), key=str)
    )
    vars: list[VarDecl] = (
        [] if single_state else [VarDecl(state_var, f"{{{state_enum}}}")]
    )

    prev_logic = []
    for v in program.local_vars + program.num_in_out:
        var = v.name
        var_type = program.symbol_table[var]
        if var_type == BOOLEAN:
            vars.append(VarDecl(var, "boolean"))
            vars.append(VarDecl(var + "_prev", "boolean"))
            vars.append(VarDecl(var + "_prev_prev", "boolean"))
        elif (
            isinstance(var_type, Number)
            and var_type.number_type in countable_number_types
        ):
            vars.append(VarDecl(var, "integer"))
            vars.append(VarDecl(var + "_prev", "integer"))
            vars.append(VarDecl(var + "_prev_prev", "integer"))
        else:
            raise Exception("Unsupported type for variable: " + str(var_type))

        prev_logic += ["next(" + str(var) + "_prev) = " + str(var)]
        prev_logic += ["next(" + str(var) + "_prev_prev) = " + str(var + "_prev")]

    vars += [
        VarDecl(str(var), "boolean") for var in program.out_events + program.bool_in_out
    ]

    init = (
        ["TRUE"]
        if single_state
        else [f"{state_var} = {state_symbols[program.initial_state]}"]
    )
    init += [
        var + " = " + str(value.to_nuxmv())
        for var, value in program.init_var_values.items()
        if not isinstance(value, NonDeterministic)
    ]
    init += ["!" + str(event) for event in program.out_events]

    trans = ["\n\t|\t".join(transitions)] + prev_logic

    invar = []
    all_numeric_vars = [str(v) for v in program.local_vars + program.num_in_out]
    invar += [
        var + " >= 0"
        for var in all_numeric_vars
        if program.symbol_table[var] == NATURAL
    ]
    invar.extend(
        [
            var + "_prev >= 0"
            for var in all_numeric_vars
            if program.symbol_table[var] == NATURAL
        ]
    )
    invar.extend(
        [
            str(var)
            + (">= " if n.interval.lower_inclusive else ">")
            + str(n.interval.lower)
            for var in all_numeric_vars
            if isinstance(n := program.symbol_table[str(var)], Number)
            and n.interval
            and n.interval.lower != ""
        ]
    )
    invar.extend(
        [
            str(var)
            + ("<= " if n.interval.upper_inclusive else "<")
            + str(n.interval.upper)
            for var in all_numeric_vars
            if isinstance(n := program.symbol_table[str(var)], Number)
            and n.interval
            and n.interval.upper != ""
        ]
    )

    return StructuredNuXmvModel(
        name=program.name,
        vars=vars,
        define=define,
        init=init,
        invar=invar,
        trans=trans,
    )


def create_nuxmv_model(program_model: StructuredNuXmvModel) -> str:
    main_model = StructuredNuXmvModel(
        name="main",
        vars=list(program_model.vars),
        define=list(program_model.define),
        init=list(program_model.init),
        invar=list(program_model.invar),
        trans=list(program_model.trans),
    )
    return render_structured_model(main_model)
