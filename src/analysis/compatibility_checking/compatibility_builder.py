from __future__ import annotations

import re

import config
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.types.ops_and_rels import BoolBiOps
from prop_lang.util import stringify_pred
from prop_lang.variable import Variable

from analysis.compatibility_checking.program_to_nuxmv import (
    program_to_nuxmv_model,
    program_state_symbol_map,
)
from analysis.compatibility_checking.renderer import (
    post_process_nuxmv,
    render_structured_model,
)
from analysis.compatibility_checking.types import (
    CompatOptions,
    StructuredNuXmvModel,
    VarDecl,
)


def _partition_state_and_transition_predicates(state_predicates, transition_predicates):
    promoted_to_transitions = []
    true_state_preds = set()
    for pred in state_predicates:
        if "_prev" in str(pred.pred):
            promoted_to_transitions.append(pred)
        else:
            true_state_preds.add(pred)
    return true_state_preds, transition_predicates.union(promoted_to_transitions)


def _extract_chain_predicate_maps(chain_preds, has_input_predicate):
    pred_rep_to_val = {}
    input_pred_rep_to_val = {}
    binned_preds = []

    for chain_pred in chain_preds:
        local_map = {}
        for pred, rep in chain_pred.bin_rep.items():
            bool_rep = stringify_pred(pred).name
            local_map[bool_rep] = pred
            binned_preds.append(f"{bool_rep} := ({rep.to_nuxmv()})")

        if has_input_predicate(chain_pred.term):
            input_pred_rep_to_val |= local_map
        else:
            pred_rep_to_val |= local_map

    return pred_rep_to_val, input_pred_rep_to_val, binned_preds


def _conjunct_terms(terms) -> str:
    if not terms:
        return "TRUE"
    rendered_terms = [f"({str(t)})" for t in terms]
    if len(rendered_terms) == 1:
        return rendered_terms[0]
    return "\n& ".join(rendered_terms)


def _indent_lines(text: str, tabs: int) -> str:
    pad = "\t" * tabs
    return "\n".join(pad + line for line in str(text).splitlines())


def _implication(lhs: str, rhs: str) -> str:
    rhs = str(rhs)
    if "\n" in rhs:
        rhs_indented = _indent_lines(rhs, 4)
        return f"({lhs}) -> (\n{rhs_indented}\n)"
    return f"({lhs}) -> ({rhs})"


def _unwrap_outer_parentheses(expr: str) -> tuple[str, bool]:
    s = str(expr).strip()
    unwrapped = False
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        encloses_whole = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if depth == 0 and i != len(s) - 1:
                encloses_whole = False
                break
            if depth < 0:
                encloses_whole = False
                break
        if not encloses_whole or depth != 0:
            break
        s = s[1:-1].strip()
        unwrapped = True
    return s, unwrapped


def _split_top_level_conjuncts(expr: str) -> list[str]:
    s = str(expr)
    parts: list[str] = []
    start = 0
    depth = 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "&" and depth == 0:
            parts.append(s[start:i].strip())
            if i + 1 < len(s) and s[i + 1] == "&":
                i += 1
            start = i + 1
        i += 1
    tail = s[start:].strip()
    if tail:
        parts.append(tail)
    return [p for p in parts if p]


def _pretty_top_level_conjuncts(expr: str) -> str:
    core, had_outer = _unwrap_outer_parentheses(expr)
    parts = _split_top_level_conjuncts(core)
    if len(parts) <= 1:
        return str(expr)
    body = "\n& ".join(parts)
    if had_outer:
        return "(\n" + body + "\n)"
    return body


def _or_terms(terms: list[str]) -> str:
    if not terms:
        return "FALSE"
    rendered_terms = [f"({t})" for t in terms]
    if len(rendered_terms) == 1:
        return rendered_terms[0]
    return "(\n" + "\n| ".join(rendered_terms) + "\n)"


def _next_to_current(expr: str) -> str:
    return re.sub(r"\bnext\s*\(", "(", str(expr))


def _parse_define_map(defines: list[str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for entry in defines:
        if ":=" not in entry:
            raise Exception(f"Unexpected define entry without ':=': {entry}")
        lhs, rhs = entry.split(":=", 1)
        lhs = lhs.strip()
        if lhs:
            out[lhs] = rhs.strip()
    return out


def _extract_dual_initial_transition_predicates(
    strategy_model: StructuredNuXmvModel, state_var: str
) -> str:
    # this should be of length one, but keeping it general here
    init_state_values: set[str] = set()
    for init_term in strategy_model.init:
        init_state_values.update(
            re.findall(
                rf"\b{re.escape(state_var)}\s*=\s*([_a-zA-Z][_a-zA-Z0-9$@\-]*)",
                str(init_term),
            )
        )

    if not init_state_values:
        return "TRUE"

    define_map = _parse_define_map(strategy_model.define)
    guard_map: dict[str, str] = {}
    act_map: dict[str, str] = {}
    for name, rhs in define_map.items():
        m_guard = re.match(r"^(.+_guard_)(\d+)$", name)
        if m_guard:
            guard_map[m_guard.group(2)] = rhs
            continue
        m_act = re.match(r"^(.+_act_)(\d+)$", name)
        if m_act:
            act_map[m_act.group(2)] = rhs

    init_transition_terms: list[str] = []
    for idx in sorted(set(guard_map.keys()).intersection(act_map.keys()), key=int):
        guard = guard_map[idx]
        act = act_map[idx]
        if not any(
            re.search(
                rf"\b{re.escape(state_var)}\s*=\s*{re.escape(init_st)}\b",
                guard,
            )
            for init_st in init_state_values
        ):
            continue

        # Use concrete transition bodies (guard/act), not guard/act macro names.
        transition_term = f"(({guard}) & ({act}))"
        init_transition_terms.append(_next_to_current(transition_term))

    if not init_transition_terms:
        raise Exception(f"No initial transition for {", ".join(init_state_values)}")
    return _or_terms(init_transition_terms)


def _module_parameter_names(
    model: StructuredNuXmvModel, extra_names: list[str] | None = None
) -> list[str]:
    names = {v.name for v in model.vars}
    if extra_names:
        names.update(extra_names)
    return sorted(names)


def _render_formula_module(
    module_name: str,
    model: StructuredNuXmvModel,
    extra_params: list[str] | None = None,
    include_invar: bool = True,
) -> str:
    params = ", ".join(_module_parameter_names(model, extra_params))
    trans_rhs = _pretty_top_level_conjuncts(_conjunct_terms(model.trans))
    defines = list(model.define) + ["__init := " + _conjunct_terms(model.init)]
    if include_invar:
        defines.append("__invar := " + _conjunct_terms(model.invar))
    defines.append("__trans := " + trans_rhs)

    def _format_define_entry(entry: str) -> str:
        text = str(entry)
        if "\n" not in text:
            return text
        lines = text.splitlines()
        first = lines[0]
        rest = lines[1:]
        return first + "\n" + "\n".join("\t\t" + line for line in rest)

    return (
        "MODULE "
        + module_name
        + "("
        + params
        + ")\n"
        + "DEFINE\n"
        + "".join("\t" + _format_define_entry(str(d)) + ";\n" for d in defines)
    )


def create_nuxmv_model_for_compatibility_checking(
    program: Program,
    strategy_model: StructuredNuXmvModel,
    state_predicates,
    transition_predicates,
    chain_preds,
    init_choice_logic_expr: str | None = None,
):
    program_model = program_to_nuxmv_model(program)

    options = CompatOptions(
        dual=config.Config.getConfig().dual,
    )

    state_predicates, transition_predicates = (
        _partition_state_and_transition_predicates(
            state_predicates,
            transition_predicates,
        )
    )

    def _has_input_preds(pred) -> bool:
        return any(v for v in pred.variablesin() if v in program.num_in_out)

    pred_rep_to_val, input_pred_rep_to_val, binned_preds = (
        _extract_chain_predicate_maps(chain_preds, _has_input_preds)
    )

    input_predicate_truth = [
        BiOp(p.pred, BoolBiOps.IFF, p.bool_var)
        for p in state_predicates
        if _has_input_preds(p)
    ]
    input_predicate_truth += [
        BiOp(p, BoolBiOps.IFF, Variable(bool_rep))
        for bool_rep, p in input_pred_rep_to_val.items()
    ]

    safety_predicate_truth = [
        BiOp(p.bool_var, BoolBiOps.IFF, p.pred)
        for p in state_predicates
        if not _has_input_preds(p)
    ]
    safety_predicate_truth += [
        BiOp(Variable(bool_rep), BoolBiOps.IFF, p)
        for bool_rep, p in pred_rep_to_val.items()
    ]

    tran_predicate_truth = [
        BiOp(bool_var, BoolBiOps.IFF, pred)
        for p in transition_predicates
        for pred, bool_var in p.bool_rep.items()
        if not _has_input_preds(p)
    ]

    used_comp_macro_names: set[str] = set()

    def _safe_macro_suffix(text: str) -> str:
        cleaned = "".join(ch if (ch.isalnum() or ch == "_") else "_" for ch in text)
        return cleaned if cleaned else "pred"

    def _fresh_comp_macro_name(lhs: str) -> str:
        base = "comp_" + _safe_macro_suffix(lhs)
        name = base
        i = 2
        while name in used_comp_macro_names:
            name = f"{base}_{i}"
            i += 1
        used_comp_macro_names.add(name)
        return name

    def _fresh_inp_comp_macro_name(lhs: str) -> str:
        base = "inp_comp_" + _safe_macro_suffix(lhs)
        name = base
        i = 2
        while name in used_comp_macro_names:
            name = f"{base}_{i}"
            i += 1
        used_comp_macro_names.add(name)
        return name

    state_pred_compat_macros: list[str] = []
    state_pred_compat_terms: list[str] = []
    for formula in safety_predicate_truth:
        lhs_name = str(formula.left) if hasattr(formula, "left") else "state_pred"
        macro_name = _fresh_comp_macro_name(lhs_name)
        state_pred_compat_macros.append(f"{macro_name} := {formula.to_nuxmv()}")
        state_pred_compat_terms.append(macro_name)

    tran_pred_compat_macros: list[str] = []
    tran_pred_compat_terms: list[str] = []
    for formula in tran_predicate_truth:
        lhs_name = str(formula.left) if hasattr(formula, "left") else "tran_pred"
        macro_name = _fresh_comp_macro_name(lhs_name)
        tran_pred_compat_macros.append(f"{macro_name} := {formula.to_nuxmv()}")
        tran_pred_compat_terms.append(macro_name)

    input_pred_compat_macros: list[str] = []
    input_pred_compat_terms: list[str] = []
    for formula in input_predicate_truth:
        lhs_name = str(formula.right) if hasattr(formula, "right") else "input_pred"
        macro_name = _fresh_inp_comp_macro_name(lhs_name)
        input_pred_compat_macros.append(f"{macro_name} := {formula.to_nuxmv()}")
        input_pred_compat_terms.append(macro_name)

    program_state_symbols = program_state_symbol_map(program.states)
    single_program_state = (
        sorted(list(program.states), key=str)[0] if len(program.states) == 1 else None
    )
    if single_program_state is None:
        program_state_aliases = [
            f"{s} := (program_state = {program_state_symbols[s]})"
            for s in program.states
        ]
    else:
        program_state_aliases = [
            f"{s} := {'TRUE' if s == single_program_state else 'FALSE'}"
            for s in program.states
        ]
    prog_state_equality = [
        f"(({s}) <-> ({program.states_binary_map[s].to_nuxmv()}))"
        for s in program.states
    ]

    compatible_states = "compatible_states := " + _conjunct_terms(prog_state_equality)
    state_pred_rhs = _conjunct_terms(state_pred_compat_terms)
    compatible_state_predicates = (
        "compatible_state_predicates := (\n" + _indent_lines(state_pred_rhs, 4) + "\n)"
    )
    compatible_tran_predicates = "compatible_tran_predicates := " + _implication(
        "!init_state",
        _conjunct_terms(tran_pred_compat_terms),
    )
    compatible_inputs = "compatible_inputs := " + _conjunct_terms(
        input_pred_compat_terms
    )
    compatible = "compatible := compatible_state_predicates & compatible_tran_predicates & compatible_states"

    prog_module_args = _module_parameter_names(program_model)
    strat_module_args = _module_parameter_names(
        strategy_model,
        ["init_state", "second_state"],
    )

    var_decls: list[VarDecl] = []
    seen_var_types: dict[str, str] = {}

    def _add_var_decl(decl: VarDecl) -> None:
        prev_typ = seen_var_types.get(decl.name)
        if prev_typ is None:
            seen_var_types[decl.name] = decl.typ
            var_decls.append(decl)
            return
        if prev_typ != decl.typ:
            raise ValueError(
                f"Conflicting types for variable '{decl.name}': {prev_typ} vs {decl.typ}"
            )

    for decl in program_model.vars:
        _add_var_decl(decl)
    program_state_names = {str(s) for s in program.states}
    for decl in strategy_model.vars:
        # Original program-state propositions are exposed in main as DEFINE aliases
        # over the enum `program_state`; do not redeclare them as free VARs.
        if decl.name in program_state_names:
            continue
        _add_var_decl(decl)
    _add_var_decl(VarDecl("init_state", "boolean"))
    _add_var_decl(VarDecl("second_state", "boolean"))
    _add_var_decl(
        VarDecl("prog_m", "ProgramModel(" + ", ".join(prog_module_args) + ")")
    )
    _add_var_decl(
        VarDecl("strat_m", "StrategyModel(" + ", ".join(strat_module_args) + ")")
    )

    prog_init = "prog_m.__init"
    prog_invar = "prog_m.__invar"
    prog_trans = "prog_m.__trans"
    strat_init = "strat_m.__init"
    strat_trans = "strat_m.__trans"

    if options.dual or init_choice_logic_expr is None:
        init_choice_logic_expr = "TRUE"
    elif isinstance(init_choice_logic_expr, bool):
        init_choice_logic_expr = "TRUE" if init_choice_logic_expr else "FALSE"
    else:
        init_choice_logic_expr = str(init_choice_logic_expr)
    init = [
        prog_init,
        strat_init,
        "init_state",
        "!second_state",
        "compatible",
        "init_choice_logic",
    ]

    invar = [prog_invar, "compatible_inputs"] + (
        [] if (options.dual) else ["!second_state"]
    )

    turn_logic = ["!next(init_state)"]
    if options.dual:
        trans_terms = [
            "init_state <-> next(second_state)",
            prog_trans,
            strat_trans,
        ] + turn_logic
        normal_trans = _conjunct_terms(trans_terms)
    else:
        new_trans = [prog_trans, strat_trans] + turn_logic
        normal_trans = _conjunct_terms(new_trans)

    model = StructuredNuXmvModel(
        name="main",
        vars=var_decls,
        define=binned_preds
        + program_state_aliases
        + state_pred_compat_macros
        + tran_pred_compat_macros
        + input_pred_compat_macros
        + [
            compatible,
            compatible_states,
            compatible_state_predicates,
            compatible_tran_predicates,
            compatible_inputs,
            "init_choice_logic := " + init_choice_logic_expr,
        ],
        init=init,
        invar=invar,
        trans=[normal_trans],
    )

    modules_text = (
        _render_formula_module("ProgramModel", program_model)
        + "\n"
        + _render_formula_module(
            "StrategyModel",
            strategy_model,
            ["init_state", "second_state"],
            include_invar=False,
        )
        + "\n"
    )
    return post_process_nuxmv(modules_text + render_structured_model(model))
