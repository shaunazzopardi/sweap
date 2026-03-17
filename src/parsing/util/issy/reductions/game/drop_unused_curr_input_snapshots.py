"""Drop unused formula-only `curr_*` input snapshot variables when no minigames exist."""

from programs.program import Program
from programs.transition import Transition
from prop_lang.formula import Formula
from prop_lang.update import Update
from prop_lang.variable import Variable


def drop_curr_input_snapshot_vars_if_no_minigames(
    program: Program,
    formula_objectives: list[Formula],
) -> tuple[Program, list[Formula], int]:
    input_var_names = {str(v) for v, _ in program.env_events}
    curr_var_names_set = {
        var_name
        for var_name in program.local_vars_str
        if var_name.startswith("curr_") and var_name[5:] in input_var_names
    }
    if len(curr_var_names_set) == 0:
        return program, formula_objectives, 0
    curr_var_names = sorted(curr_var_names_set)

    source_transitions = (
        list(program.orig_ts)
        if hasattr(program, "orig_ts")
        else list(program.transitions)
    )

    # Keep curr_* variables that are semantically used (read) by transition logic.
    curr_vars_to_keep = set()
    for t in source_transitions:
        for v in t.condition.variablesin():
            v_name = str(v)
            if v_name in curr_var_names_set:
                curr_vars_to_keep.add(v_name)
        for p in t.pred_upgrades:
            for v in p.variablesin():
                v_name = str(v)
                if v_name in curr_var_names_set:
                    curr_vars_to_keep.add(v_name)
        for u in t.action:
            for v in u.right.variablesin():
                v_name = str(v)
                if v_name in curr_var_names_set:
                    curr_vars_to_keep.add(v_name)

    removable_curr_vars = [v for v in curr_var_names if v not in curr_vars_to_keep]
    if len(removable_curr_vars) == 0:
        return program, formula_objectives, 0

    replace_map = {}
    for curr_name in removable_curr_vars:
        inp_name = curr_name[5:]
        replace_map[Variable(curr_name)] = Variable(inp_name)
        replace_map[Variable(curr_name + "'")] = Variable(inp_name + "'")
        replace_map[Variable(curr_name + "_prev")] = Variable(inp_name + "_prev")

    rewritten_objectives = [f.replace_formulas(replace_map) for f in formula_objectives]

    rewritten_transitions = []
    for t in source_transitions:
        rewritten_condition = t.condition.replace_formulas(replace_map)
        rewritten_actions = []
        for u in t.action:
            if str(u.left) in removable_curr_vars:
                continue
            new_left = u.left.replace_formulas(replace_map)
            new_right = u.right.replace_formulas(replace_map)
            rewritten_actions.append(Update(new_left, new_right))

        new_t = Transition(
            t.src,
            rewritten_condition,
            rewritten_actions,
            list(t.output),
            t.tgt,
        )
        if len(t.pred_upgrades) > 0:
            new_t.set_predicate_upgrades(
                [p.replace_formulas(replace_map) for p in t.pred_upgrades]
            )
        rewritten_transitions.append(new_t)

    init_values = []
    for var_name in program.local_vars_str:
        if var_name in removable_curr_vars:
            continue
        var_type = program.symbol_table[var_name]
        if var_name in program.init_var_values:
            init_values.append((var_name, var_type, program.init_var_values[var_name]))
        else:
            init_values.append((var_name, var_type))

    rewritten_program = Program(
        program.name,
        set(program.states),
        program.initial_state,
        init_values,
        rewritten_transitions,
        list(program.env_events),
        list(program.con_events),
        preprocess=False,
        emit_state_binary_map=False,
    )
    return rewritten_program, rewritten_objectives, len(removable_curr_vars)

