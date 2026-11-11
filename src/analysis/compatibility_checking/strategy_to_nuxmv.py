from __future__ import annotations

import config
from analysis.smt_checker import quantifier_elimination
from pysmt.shortcuts import And, Exists, Symbol
from pysmt.typing import BOOL
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    fnode_to_formula,
    disjunct_formula_set,
    conjunct,
    is_tautology,
    massage_ltl_for_dual,
    simplify_formula_without_math,
    sat,
    true,
)
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from synthesis.machines.machine import Machine
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine

from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl


def _or(parts: list[str]) -> str:
    if not parts:
        return "FALSE"
    return "((" + ")\n\t|\t(".join(parts) + "))"


def _mode() -> str:
    dual = config.Config.getConfig().dual
    if dual:
        return "dual"
    return "base"


def _state_var_name(mode: str) -> str:
    return "strategy_state"


def _state_enum_decl(states: set, state_var: str) -> VarDecl:
    enum_vals = ", ".join(s for s in sorted(states, key=str))
    return VarDecl(state_var, f"{{{enum_vals}}}")


def _single_state_value(states: set) -> str | None:
    if len(states) != 1:
        return None
    return sorted(states, key=str)[0]


def _append_var_decl(
    decls: list[VarDecl], seen_types: dict[str, str], name: str, typ: str
) -> None:
    prev_typ = seen_types.get(name)
    if prev_typ is None:
        seen_types[name] = typ
        decls.append(VarDecl(name, typ))
        return
    if prev_typ != typ:
        raise ValueError(
            f"Conflicting types for variable '{name}': {prev_typ} vs {typ}"
        )


def _to_total_smt(formula, symbol_table):
    expr, invar = formula.to_smt(symbol_table)
    return expr if invar.is_true() else And(expr, invar)


def _project_out_env_props(formula, env_props):
    symbol_table = {str(v): BOOLEAN for v in formula.variablesin()}
    env_names = {str(v) for v in env_props}
    quantified = [
        Symbol(name, BOOL)
        for name in sorted(env_names.intersection(symbol_table.keys()))
    ]
    smt = _to_total_smt(formula, symbol_table)
    if quantified:
        smt = quantifier_elimination(Exists(quantified, smt))
    return simplify_formula_without_math(fnode_to_formula(smt))


def _dual_init_qe_quantified_props(
    machine: Machine,
    pred_acts,
    prog_states,
    keep_var_names: set[str] | None = None,
):
    keep_names = {str(v) for v in pred_acts}
    keep_names.update(str(s) for s in prog_states)
    keep_names.update(
        str(v)
        for v in machine.con_events
        if str(v).startswith("pred__") or str(v).startswith("bin_")
    )
    if keep_var_names:
        keep_names.update(str(v) for v in keep_var_names)

    quantified = list(machine.env_events)
    quantified.extend(
        v
        for v in machine.con_events
        if (str(v) not in keep_names)
        and (not str(v).startswith("pred__"))
        and (not str(v).startswith("bin_"))
    )
    return quantified


def _dual_init_qe_quantified_env_init_props(machine: Machine):
    env_init_from_env = [
        v for v in machine.env_events if str(v).startswith("env_init_")
    ]
    env_init_from_con = [
        v for v in machine.con_events if str(v).startswith("env_init_")
    ]
    seen = set()
    quantified = []
    for v in env_init_from_env + env_init_from_con:
        n = str(v)
        if n in seen:
            continue
        seen.add(n)
        quantified.append(v)
    return quantified


def _mealy_to_nuxmv_tandem_model(
    machine: MealyMachine,
    prog_states,
    prog_out_events,
    state_pred_list,
    trans_pred_list,
    *,
    state_var: str,
    next_shift_pred_bin_vars: bool,
    init_choice_logic=None,
) -> StructuredNuXmvModel:
    state_pred_acts = [p.bool_var for p in state_pred_list]
    trans_pred_acts = [t for p in trans_pred_list for t in p.bool_rep.values()]
    pred_acts = state_pred_acts + trans_pred_acts

    dual_next_events = set(pred_acts).union(
        v
        for v in machine.con_events
        if str(v).startswith("pred__") or str(v).startswith("bin_")
    )
    guards_acts = {}
    init_transition_terms_by_tgt: dict[str, list] = {}
    single_state = _single_state_value(machine.states)

    # In dual, only state-predicate/bin vars are shifted to next-step facts.
    strip_next = lambda f: (
        f.right if isinstance(f, UniOp) and (f.op == "next" or f.op == "X") else None
    )

    debug = config.Config.getConfig().debug
    for src in machine.transitions.keys():
        if debug:
            ecs = [
                ec
                for env_con_behs in machine.transitions[src].values()
                for ec, _ in env_con_behs
            ]
            c = disjunct_formula_set(ecs)
            symbol_table = {str(v): BOOLEAN for v in c.variablesin()}
            if not is_tautology(c, symbol_table):
                raise Exception(
                    str(src)
                    + " does not have complete transitions for environment behaviour."
                )
            for e1 in ecs:
                for e2 in ecs:
                    if e1 != e2:
                        cc = conjunct(e1, e2)
                        symbol_table = {str(v): BOOLEAN for v in cc.variablesin()}
                        if sat(cc, symbol_table):
                            raise Exception(
                                str(src)
                                + " has overlapping transitions for environment behaviour: "
                                + str(e1)
                                + " and "
                                + str(e2)
                            )

        for tgt, env_con_behs in machine.transitions[src].items():
            if debug:
                for ec, _ in env_con_behs:
                    for ecc, _ in env_con_behs:
                        if ec != ecc:
                            cc = conjunct(ec, ecc)
                            symbol_table = {str(v): BOOLEAN for v in cc.variablesin()}
                            if sat(cc, symbol_table):
                                raise Exception(
                                    str(src)
                                    + " has conflicting transitions: "
                                    + str(ec)
                                    + " and "
                                    + str(ecc)
                                )

            for env_beh, con_beh in env_con_behs:
                guard_formula = (
                    massage_ltl_for_dual(con_beh, dual_next_events, False)
                    if next_shift_pred_bin_vars
                    else con_beh
                )
                con_beh_effect = (
                    massage_ltl_for_dual(con_beh, dual_next_events, False)
                    if next_shift_pred_bin_vars
                    else con_beh
                )
                con_beh_nuxmv = guard_formula.to_nuxmv()
                state_guard = (
                    "TRUE" if single_state is not None else f"{state_var} = {src}"
                )
                guard = state_guard + " & " + str(env_beh) + " & " + con_beh_nuxmv
                if guard not in guards_acts:
                    guards_acts[guard] = []

                act = (
                    "TRUE"
                    if single_state is not None
                    else f"(next({state_var}) = {tgt})"
                )

                guards_acts[guard].append(act)
                if next_shift_pred_bin_vars and src == machine.init_st:
                    init_transition_terms_by_tgt.setdefault(tgt, []).append(
                        conjunct(
                            env_beh,
                            con_beh_effect.replace_formulas(strip_next),
                        )
                    )

    define = []
    transition_refs = []
    i = 0
    guard_keys = list(guards_acts.keys())
    while i < len(guard_keys):
        define += [machine.name + "_guard_" + str(i) + " := " + guard_keys[i]]
        define += [
            machine.name
            + "_act_"
            + str(i)
            + " := ("
            + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]]))
            + ")"
        ]
        transition_refs.append(
            machine.name + "_guard_" + str(i) + " & " + machine.name + "_act_" + str(i)
        )
        i += 1

    vars: list[VarDecl] = []
    seen_var_types: dict[str, str] = {}
    excluded_env_names = {str(v) for v in (prog_out_events + prog_states + pred_acts)}
    if single_state is None:
        state_decl = _state_enum_decl(machine.states, state_var)
        _append_var_decl(vars, seen_var_types, state_decl.name, state_decl.typ)
    for var in machine.env_events:
        var_s = str(var)
        if var_s not in excluded_env_names:
            _append_var_decl(vars, seen_var_types, var_s, "boolean")
    for var in machine.con_events:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")
    for var in prog_out_events:
        _append_var_decl(vars, seen_var_types, "prog_" + str(var), "boolean")
    for var in prog_states:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")
    for var in pred_acts:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")

    if next_shift_pred_bin_vars:
        init_choice = init_choice_logic if init_choice_logic is not None else true()
        qe_quantified_props = _dual_init_qe_quantified_props(
            machine, pred_acts, prog_states
        )
        projected_init_terms: list[str] = []
        for tgt, tgt_terms in init_transition_terms_by_tgt.items():
            combined = conjunct(init_choice, disjunct_formula_set(tgt_terms))
            projected = _project_out_env_props(combined, qe_quantified_props)
            if isinstance(projected, Value) and projected.is_false():
                continue
            if isinstance(projected, Value) and projected.is_true():
                if single_state is not None:
                    projected_init_terms.append("TRUE")
                else:
                    projected_init_terms.append(f"({state_var} = {tgt})")
            else:
                if single_state is not None:
                    projected_init_terms.append(f"({projected.to_nuxmv()})")
                else:
                    projected_init_terms.append(
                        f"(({state_var} = {tgt}) & ({projected.to_nuxmv()}))"
                    )

        if not projected_init_terms:
            raise Exception(
                "Something wrong in LTL, no valid controller choice for initial state precicates"
            )
        init_cond = _or(projected_init_terms)
    else:
        init_cond = (
            "TRUE" if single_state is not None else f"{state_var} = {machine.init_st}"
        )
    init = [init_cond]
    transitions_formula = _or(transition_refs)
    trans_logic = transitions_formula
    trans = [trans_logic]
    invar = ["TRUE"]

    return StructuredNuXmvModel(
        name=machine.name,
        vars=vars,
        define=define,
        init=init,
        invar=invar,
        trans=trans,
    )


def _moore_to_nuxmv_tandem_model(
    machine: MooreMachine,
    prog_states,
    prog_out_events,
    state_pred_list,
    trans_pred_list,
    *,
    state_var: str,
    init_choice_logic=None,
    project_init_with_qe: bool = False,
) -> StructuredNuXmvModel:
    state_pred_acts = [p.bool_var for p in state_pred_list]
    trans_pred_acts = [t for p in trans_pred_list for t in p.bool_rep.values()]
    pred_acts = state_pred_acts + trans_pred_acts
    dual_mode = config.Config.getConfig().dual
    base_mode = not dual_mode
    dual_guard_next_events = set(pred_acts).union(
        v
        for v in machine.con_events
        if str(v).startswith("pred__") or str(v).startswith("bin_")
    )

    guards_acts = {}
    single_state = _single_state_value(machine.states)

    init_cond_terms: list[str] = []
    strip_next = lambda f: (
        f.right if isinstance(f, UniOp) and (f.op == "next" or f.op == "X") else None
    )
    if project_init_with_qe:
        init_choice = init_choice_logic if init_choice_logic is not None else true()
        qe_quantified_props = _dual_init_qe_quantified_props(
            machine, pred_acts, prog_states, keep_var_names=set()
        )
        qe_quantified_out_props = _dual_init_qe_quantified_env_init_props(machine)
        init_transition_terms_by_tgt: dict[str, list] = {}
        for src in machine.init_st:
            for con_beh, tgt in machine.transitions.get(src, []):
                init_transition_terms_by_tgt.setdefault(tgt, []).append(
                    conjunct(con_beh, machine.out[src])
                )

        for tgt, tgt_terms in init_transition_terms_by_tgt.items():
            combined = conjunct(init_choice, disjunct_formula_set(tgt_terms))
            combined = combined.replace_formulas(strip_next)
            projected = _project_out_env_props(combined, qe_quantified_props)
            if isinstance(projected, Value) and projected.is_false():
                continue
            if isinstance(projected, Value) and projected.is_true():
                init_term = (
                    "TRUE" if single_state is not None else f"({state_var} = {tgt})"
                )
            else:
                init_term = (
                    f"({projected.to_nuxmv()})"
                    if single_state is not None
                    else f"({state_var} = {tgt}) & ({projected.to_nuxmv()})"
                )
            projected_out = _project_out_env_props(
                machine.out[tgt], qe_quantified_out_props
            )
            init_term += f" & ({projected_out.to_nuxmv()})"
            init_cond_terms.append(init_term)

        if not init_cond_terms:
            raise Exception(
                "Something wrong in LTL, no valid controller choice for initial state precicates"
            )
    else:
        for st in machine.init_st:
            st_guard = machine.out[st]
            if single_state is not None:
                init_cond_terms.append(f"({st_guard.to_nuxmv()})")
            else:
                init_cond_terms.append(f"({state_var} = {st} & {st_guard.to_nuxmv()})")
    if base_mode:
        base_init_terms: list[str] = []
        for st in sorted(machine.init_st, key=str):
            st_out = machine.out[st].to_nuxmv()
            if single_state is not None:
                base_init_terms.append(f"({st_out})")
            else:
                base_init_terms.append(f"(({state_var} = {st}) & ({st_out}))")
        init_cond = _or(base_init_terms)
    else:
        init_cond = _or(init_cond_terms)

    debug = config.Config.getConfig().debug
    for src in machine.transitions.keys():
        if debug:
            ccs = [cc for cc, _ in machine.transitions[src]]
            c = disjunct_formula_set(ccs)
            symbol_table = {str(v): BOOLEAN for v in c.variablesin()}
            if not is_tautology(c, symbol_table):
                raise Exception(
                    str(src)
                    + " does not have complete transitions for controller behaviour."
                )
            for c1 in ccs:
                for c2 in ccs:
                    if c1 != c2:
                        overlap = conjunct(c1, c2)
                        symbol_table = {str(v): BOOLEAN for v in overlap.variablesin()}
                        if sat(overlap, symbol_table):
                            raise Exception(
                                str(src)
                                + " has overlapping transitions for controller behaviour: "
                                + str(c1)
                                + " and "
                                + str(c2)
                            )

        for con_beh, tgt in machine.transitions[src]:
            guard_formula = (
                massage_ltl_for_dual(con_beh, dual_guard_next_events, False)
                if dual_mode
                else con_beh
            )
            state_guard = "TRUE" if single_state is not None else f"{state_var} = {src}"
            guard = state_guard + " & " + guard_formula.to_nuxmv()
            if guard not in guards_acts:
                guards_acts[guard] = []

            next_state = machine.out[tgt].replace(lambda x: UniOp("next", x))
            act = (
                f"({next_state.to_nuxmv()})"
                if single_state is not None
                else f"({next_state.to_nuxmv()}) & (next({state_var}) = {tgt})"
            )

            guards_acts[guard].append(act)

    define = []
    transition_refs = []
    i = 0
    guard_keys = list(guards_acts.keys())
    while i < len(guard_keys):
        define += [machine.name + "_guard_" + str(i) + " := " + guard_keys[i]]
        define += [
            machine.name
            + "_act_"
            + str(i)
            + " := ("
            + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]]))
            + ")"
        ]
        transition_refs.append(
            machine.name + "_guard_" + str(i) + " & " + machine.name + "_act_" + str(i)
        )
        i += 1

    vars: list[VarDecl] = []
    seen_var_types: dict[str, str] = {}
    excluded_env_names = {str(v) for v in (prog_out_events + prog_states + pred_acts)}
    if single_state is None:
        state_decl = _state_enum_decl(machine.states, state_var)
        _append_var_decl(vars, seen_var_types, state_decl.name, state_decl.typ)
    for var in machine.env_events:
        var_s = str(var)
        if var_s not in excluded_env_names:
            _append_var_decl(vars, seen_var_types, var_s, "boolean")
    for var in machine.con_events:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")
    for var in prog_out_events:
        _append_var_decl(vars, seen_var_types, "prog_" + str(var), "boolean")
    for var in prog_states:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")
    for var in pred_acts:
        _append_var_decl(vars, seen_var_types, str(var), "boolean")

    init = [init_cond]
    transitions_formula = _or(transition_refs)
    trans_logic = transitions_formula
    trans = [trans_logic]
    invar = ["TRUE"]

    return StructuredNuXmvModel(
        name=machine.name,
        vars=vars,
        define=define,
        init=init,
        invar=invar,
        trans=trans,
    )


def strategy_to_nuxmv_model(
    strategy_machine: Machine,
    prog_states,
    prog_out_events,
    state_pred_list,
    trans_pred_list,
    *,
    for_verification: bool = False,
    init_choice_logic=None,
) -> StructuredNuXmvModel:
    mode = _mode()
    state_var = _state_var_name(mode)

    if for_verification:
        if isinstance(strategy_machine, MealyMachine):
            return _mealy_to_nuxmv_tandem_model(
                strategy_machine,
                prog_states,
                prog_out_events,
                state_pred_list,
                trans_pred_list,
                state_var=state_var,
                next_shift_pred_bin_vars=(mode == "dual"),
                init_choice_logic=init_choice_logic,
            )
        if isinstance(strategy_machine, MooreMachine):
            return _moore_to_nuxmv_tandem_model(
                strategy_machine,
                prog_states,
                prog_out_events,
                state_pred_list,
                trans_pred_list,
                state_var=state_var,
                init_choice_logic=init_choice_logic,
                project_init_with_qe=(mode == "dual"),
            )
        raise TypeError(
            "verification expects strategy machine to be MealyMachine or MooreMachine"
        )

    if mode == "dual":
        if not isinstance(strategy_machine, MealyMachine):
            raise TypeError("dual compatibility expects a MealyMachine strategy")
        return _mealy_to_nuxmv_tandem_model(
            strategy_machine,
            prog_states,
            prog_out_events,
            state_pred_list,
            trans_pred_list,
            state_var=state_var,
            next_shift_pred_bin_vars=True,
            init_choice_logic=init_choice_logic,
        )

    if not isinstance(strategy_machine, MooreMachine):
        raise TypeError("base compatibility expects a MooreMachine strategy")

    return _moore_to_nuxmv_tandem_model(
        strategy_machine,
        prog_states,
        prog_out_events,
        state_pred_list,
        trans_pred_list,
        state_var=state_var,
        init_choice_logic=init_choice_logic,
        project_init_with_qe=False,
    )
