import itertools
import logging
import math
import os
import pickle
import re
import shutil
from itertools import chain, combinations

from pysmt.factory import SolverRedefinitionError
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import get_env, And
from sympy.utilities.iterables import iterable

from analysis.smt_checker import check, bdd_simplify
import config
from programs.binary_rep_map import BinaryRepMap
from programs.dfa import (
    classify_initial_values,
    classify_initial_values_with_ltl_horizon,
)
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, Type
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.util import (
    atomic_predicates,
    conjunct_formula_set,
    conjunct,
    dnf_safe,
    neg,
    append_to_variable_name,
    dnf,
    disjunct_formula_set,
    true,
    sat,
    is_tautology,
    iff,
    propagate_negations,
    type_constraints_formula,
    var_to_predicate,
    fnode_to_formula,
    run_with_timeout,
    false,
    disjunct,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


def symbol_table_from_program(
    program, init_values
) -> tuple[dict[str, Type], dict[str, Value], list[str]]:
    symbol_table = dict()
    init_var_values = dict()
    unset_init_vars = []
    for state in program.states:
        symbol_table[state] = BOOLEAN
    for ev, t in program.out_events + program.env_events + program.con_events:
        symbol_table[ev.name] = t
        if t is not BOOLEAN:
            symbol_table[ev.name + "_prev"] = t
            symbol_table[ev.name + "_prev" + "_prev"] = t
    for v in init_values:
        var_name = v[0]
        var_type = v[1]
        if len(v) == 3:
            init_var_values[var_name] = v[2]
        else:
            unset_init_vars.append(v[0])
        symbol_table[var_name] = var_type
        symbol_table[var_name + "_prev"] = var_type
        symbol_table[var_name + "_prev" + "_prev"] = var_type

    return symbol_table, init_var_values, unset_init_vars


def ce_state_to_predicate_abstraction_trans(
    ltl_to_program_transitions,
    symbol_table,
    start,
    middle,
    end,
    env_events,
    con_events,
):
    # ltl_to_program_transitions is a dict of the form {now: {(con_ev, env_ev) : [(con_trans, env_trans)]}}
    start = conjunct_formula_set(
        [
            Variable(key.removeprefix("mon_"))
            for key, value in start.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "TRUE"
        ]
        + [
            neg(Variable(key.removeprefix("mon_")))
            for key, value in start.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "FALSE"
        ]
    )
    middle = conjunct_formula_set(
        [
            Variable(key.removeprefix("mon_"))
            for key, value in middle.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "TRUE"
        ]
        + [
            neg(Variable(key.removeprefix("mon_")))
            for key, value in middle.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "FALSE"
        ]
    )
    end = conjunct_formula_set(
        [
            Variable(key.removeprefix("mon_"))
            for key, value in end.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "TRUE"
        ]
        + [
            neg(Variable(key.removeprefix("mon_")))
            for key, value in end.items()
            if (
                key.startswith("mon_")
                or key.startswith("pred_")
                or Variable(key) in env_events + con_events
            )
            and value == "FALSE"
        ]
    )

    for abs_con_start in ltl_to_program_transitions.keys():
        if abs_con_start == "init":
            continue
        if check(And(*(conjunct(abs_con_start, start).to_smt(symbol_table)))):
            for abs_env_start, abs_env_end in ltl_to_program_transitions[
                abs_con_start
            ].keys():
                if check(And(*(conjunct(abs_env_start, middle).to_smt(symbol_table)))):
                    if check(And(*(conjunct(abs_env_end, end).to_smt(symbol_table)))):
                        return ltl_to_program_transitions[abs_con_start][
                            (abs_env_start, abs_env_end)
                        ]

    return []


def parse_nuxmv_ce_output_finite(
    program,
    out,
    cs_alphabet,
    monitor_turn="cs",
    injected_cs_constants: dict[str, str] | None = None,
):
    prefix, _ = get_ce_from_nuxmv_output(out)

    (
        agreed_on_transitions,
        incompatible_state,
    ) = prog_transition_indices_and_state_from_ce(
        program,
        prefix,
        cs_alphabet,
        monitor_turn,
        injected_cs_constants=injected_cs_constants,
    )

    return agreed_on_transitions, incompatible_state


def prog_transition_indices_and_state_from_ce(
    program,
    prefix,
    cs_alphabet,
    monitor_turn="cs",
    injected_cs_constants: dict[str, str] | None = None,
):
    def _canonical_key(key: str) -> str:
        # nuXmv module instances expose local symbols as "instance.symbol".
        # We normalize those to plain symbol names for downstream processing.
        return key.rsplit(".", 1)[-1]

    def _scope_segments(key: str):
        parts = key.split(".")
        return parts[:-1], parts[-1]

    def _is_program_scoped(key: str) -> bool:
        scope, _ = _scope_segments(key)
        if not scope:
            return True
        return "prog_m" in scope and "strat_m" not in scope

    def _program_guard_index(key: str):
        # Accept unqualified and nested-qualified program guards:
        #   guard_i, prog_m.guard_i, main.prog_m.guard_i, ...
        if not _is_program_scoped(key):
            return None
        match = re.match(r"^(?:[A-Za-z_][A-Za-z0-9_]*\.)*guard_(\d+)$", key)
        return match.group(1) if match else None

    def _has_matching_program_act(
        dic: dict[str, str], guard_key: str, idx: str
    ) -> bool:
        _, guard_tail = _scope_segments(guard_key)
        act_tail = guard_tail.replace("guard_", "act_", 1)
        # Fast path: same scope path as guard.
        if "." in guard_key:
            guard_scope = guard_key.rsplit(".", 1)[0]
            if dic.get(guard_scope + "." + act_tail) == "TRUE":
                return True
        else:
            if dic.get(act_tail) == "TRUE":
                return True
        # Robust path: any program-scoped key with matching act tail.
        for k, v in dic.items():
            if v != "TRUE":
                continue
            if not _is_program_scoped(k):
                continue
            _, tail = _scope_segments(k)
            if tail == act_tail:
                return True
        return False

    transition_no = len(program.transitions)
    program_alphabet = (
        [str(s) for s in program.states] + ["program_state"] + program.local_vars_str
    )

    program_states = []
    program_transitions = []
    cs_states = []

    if len(prefix) == 0:
        raise Exception("Counterexample has no state.")

    if prefix[0]["compatible"] == "FALSE":
        raise Exception(
            "Initial state is not compatible with the program. "
            "This most probably indicates a problem with sweap, or with the synthesis backend."
        )

    numerical_in_outs = [str(v) for v in program.num_in_out]
    for dic in prefix:
        # monitor only makes decisions at env and mon turns
        if "turn" not in dic.keys() or dic["turn"] == monitor_turn:
            transition = "-1"
            program_state = {}
            cs_state = {}
            for key, value in dic.items():
                ckey = _canonical_key(key)
                if ckey.split("_prev")[0] in program_alphabet:
                    program_state[ckey] = value
                elif (
                    ckey in cs_alphabet
                    or ckey in {"init_state", "second_state"}
                    or ckey.startswith("compatible")
                    or ckey.startswith("comp_")
                    or ckey.startswith("inp_comp_")
                    or ckey.startswith("pred")
                    or ckey in numerical_in_outs
                ):
                    cs_state[ckey] = value

                guard_idx = _program_guard_index(key)
                if guard_idx is not None and value == "TRUE":
                    if _has_matching_program_act(dic, key, guard_idx):
                        if guard_idx != str(transition_no):
                            transition = guard_idx

            # Tandem v2 can encode program control state as an enum variable.
            # Reconstruct legacy one-hot view expected downstream.
            if "program_state" in program_state:
                current = program_state["program_state"]
                for st in program.states:
                    s = str(st)
                    if s not in program_state:
                        program_state[s] = "TRUE" if current == s else "FALSE"

            if injected_cs_constants:
                for k, v in injected_cs_constants.items():
                    cs_state.setdefault(k, v)

            program_states.append(program_state)
            cs_states.append(cs_state)
            program_transitions.append(transition)

    return (program_transitions[:-1], program_states[:-1], cs_states[:-1]), (
        program_transitions[-1],
        program_states[-1],
        cs_states[-1],
    )


def full_ce_from_nuxmv_output(out: str):
    ce = out.split("Counterexample")[1].strip()
    # ce = re.sub("[^\n]*(act|guard)\_[0-9]+ = [^\n]+", "", ce)
    ce = re.sub("[^\n]*(identity)_[^\n]+", "", ce)
    split_ce = ce.split("-- Loop starts here")
    prefix = split_ce[0]

    prefix = re.split("[^\n]*->[^<]*<-", prefix)
    prefix = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in prefix]
    prefix.remove([])
    prefix = [
        dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t])
        for t in prefix
    ]

    if len(split_ce) == 1:
        return complete_ce(prefix, [])
    loop = split_ce[1]
    loop = re.split("[^\n]*->[^<]*<-", loop)
    loop = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in loop]
    loop.remove([])
    loop = [
        dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t])
        for t in loop
    ]

    return complete_ce(prefix, loop)


def get_ce_from_nuxmv_output(out: str):
    complete_prefix, complete_loop = full_ce_from_nuxmv_output(out)

    prune_up_to_mismatch = []
    for i in range(0, len(complete_prefix)):
        if complete_prefix[i]["compatible"] == "TRUE":
            prune_up_to_mismatch += [complete_prefix[i]]
        else:
            prune_up_to_mismatch += [complete_prefix[i]]  # add mismatching state
            break
    return (
        prune_up_to_mismatch,
        complete_prefix[len(prune_up_to_mismatch) :] + complete_loop,
    )


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        complete_ce_state(prefix[i - 1], prefix[i])

    if loop:
        complete_ce_state(prefix[-1], loop[0])

        for i in range(1, len(loop)):
            complete_ce_state(loop[i - 1], loop[i])

    return prefix, loop


def complete_ce_state(state, next_state):
    missing = dict([(k, state[k]) for k in state.keys() if k not in next_state.keys()])
    next_state.update(missing)


def only_this_state(states, state):
    only_this_state = str(state)
    for other in states:
        if other != state:
            only_this_state += " & !(" + str(other) + ")"
    return only_this_state


def only_this_state_next(states, state):
    only_this_state = "next(" + str(state) + ")"
    for other in states:
        if other != state:
            only_this_state += " & !next(" + str(other) + ")"
    return only_this_state


def get_differently_value_vars(state1: dict, state2: dict):
    return [
        key
        for key in state1.keys()
        if key in state2.keys() and state1[key] != state2[key]
    ]


def _check_os():
    if os.name not in ("posix", "nt"):
        raise Exception(f"This test does not support OS '{os.name}'.")


def _add_solver(description, command, args=[], logics=None):
    _check_os()
    logics = logics or [QF_UFLRA]

    path = shutil.which(command)

    # Add the solver to the environment
    env = get_env()
    try:
        env.factory.add_generic_solver(description, [path, *args], logics)
    except SolverRedefinitionError:
        # Solver has already been registered, skip
        pass


def ce_state_to_formula(state: dict, symbol_table: dict) -> Formula:
    formula = None
    for key, value in state.items():
        if key not in symbol_table.keys():
            continue
        conjunctt = BiOp(Variable(key), "=", Value(value))
        if formula is None:
            formula = conjunctt
        else:
            formula = conjunct(formula, conjunctt)
    return formula


def ground_formula_on_ce_state_with_index(formula: Formula, state: dict, i) -> Formula:
    to_replace_with = []
    for key, value in state.items():
        to_replace_with.append(Update(Variable(key + "_" + str(i)), Value(value)))
    return formula.replace(to_replace_with)


def reduce_up_to_iff(old_preds, new_preds, symbol_table, tautology_check=True):
    if len(new_preds) == 0:
        return old_preds

    keep_these = set()
    remove_these = set()

    for p in set(new_preds):
        if (
            p
            and neg(p) not in remove_these
            and not isinstance(p, Value)
            and not isinstance(neg(p), Value)
            and not has_equiv_pred(p, set(old_preds) | keep_these, symbol_table)
            and (
                not tautology_check
                or not (
                    is_tautology(p, symbol_table) or is_tautology(neg(p), symbol_table)
                )
            )
        ):
            keep_these.add(p)
        else:
            remove_these.add(p)
            remove_these.add(neg(p))

    return keep_these | set(old_preds)


def has_equiv_pred(p, preds, symbol_table):
    if p in preds or neg(p) in preds:
        return True

    for pp in preds:
        # technically should check if it can be expressed using a set of the existing predicates, but can be expensive
        if is_tautology(iff(p, pp), symbol_table) or is_tautology(
            iff(neg(p), pp), symbol_table
        ):
            return True

    return False


def project_ce_state_onto_ev(state: dict, events):
    return {k: v for k, v in state.items() if Variable(k) in events}


def stutter_transitions(program, env: bool):
    stutter_transitions = []
    for state in program.states:
        st = stutter_transition(program, state, env)
        if st != None:
            stutter_transitions.append(st)
    return stutter_transitions


stutter_transition_cache = {}


def bdd_simplify_guards(program, guard):
    if len(guard.variablesin()) == 0:
        return guard
    fnode = And(*guard.to_smt(program.symbol_table))
    order = [
        v
        for v in fnode.get_free_variables()
        if Variable(str(v)) in program.env_events + program.con_events
    ]
    condition_simplified = bdd_simplify(fnode, static_ordering=order)
    if condition_simplified is not None:
        condition_simplified = fnode_to_formula(condition_simplified)
        print(
            "simplified "
            + str(guard)
            + " (len "
            + str(len(guard))
            + ") to "
            + str(condition_simplified)
            + " (len "
            + str(len(condition_simplified))
            + ")"
        )
        return condition_simplified
    else:
        return guard


def bdd_simplify_native(guard, symbol_table):
    fnode = guard.to_smt(symbol_table)[0]
    condition_simplified = bdd_simplify(fnode)
    if condition_simplified is not None:
        condition_simplified = fnode_to_formula(condition_simplified)
        print(
            "simplified "
            + str(guard)
            + " (len "
            + str(len(guard))
            + ") to "
            + str(condition_simplified)
            + " (len "
            + str(len(condition_simplified))
            + ")"
        )
        return condition_simplified
    else:
        return guard


def stutter_transition(program, state, cnf=False):
    # If the program already materialized explicit stutter transitions,
    # reuse that transition directly.
    if hasattr(program, "stutter_ts"):
        for t in program.stutter_ts:
            if t.src == state and t.tgt == state:
                return t

    # Otherwise derive stutter from non-stutter transitions only.
    transitions = getattr(program, "orig_ts", program.transitions)
    condition = neg(
        disjunct_formula_set([t.condition for t in transitions if t.src == state])
    )

    if program not in stutter_transition_cache.keys():
        stutter_transition_cache[program] = {}

    cache_key = (state, condition, cnf)
    if cache_key in stutter_transition_cache[program].keys():
        return stutter_transition_cache[program][cache_key]

    cond_fnode = And(*condition.to_smt(program.symbol_table))

    if check(cond_fnode):
        if cnf:
            args = [program, condition]
            success, condition_simplified = run_with_timeout(
                bdd_simplify_guards, args, timeout=0.2
            )
            if success:
                condition = condition_simplified
        stutter_t = (
            Transition(state, condition, [], [], state)
            .complete_outputs(program.out_events)
            .complete_action_set([v for v in program.local_vars])
        )
        stutter_transition_cache[program][cache_key] = stutter_t
        return stutter_t
    else:
        stutter_transition_cache[program][cache_key] = None
        return None


def looping_to_normal(t: Transition):
    return t  # Transition(re.split("_loop", t.src)[0], t.condition, t.action, t.output,  re.split("_loop", t.tgt)[0]) \
    #  if "loop" in ((t.src) + (t.tgt)) else t


def preds_in_state(ce_state: dict[str, str]):
    return [
        var_to_predicate(Variable(p))
        for p, v in ce_state.items()
        if p.startswith("pred_") and v == "TRUE"
    ] + [
        neg(var_to_predicate((Variable(p))))
        for p, v in ce_state.items()
        if p.startswith("pred_") and v == "FALSE"
    ]


def ground_transitions(
    program, transition_and_state_list, vars_to_ground_on, symbol_table
):
    grounded = []
    for t, st in transition_and_state_list:
        projected_condition = ground_predicate_on_vars(
            program, t.condition, st, vars_to_ground_on, symbol_table
        )
        grounded += [
            Transition(
                t.src,
                projected_condition,
                [a for a in t.action if str(a.left) not in vars_to_ground_on],
                t.output,
                t.tgt,
            )
        ]
    return grounded


def ground_predicate_on_vars(program, predicate, ce_state, vars, symbol_table):
    grounded_state = project_ce_state_onto_ev(
        ce_state,
        program.env_events
        + program.con_events
        + program.out_events
        + [Variable(str(v)) for v in vars],
    )
    projected_condition = predicate.replace(
        {Variable(key): Value(grounded_state[key]) for key in grounded_state.keys()}
    )
    return projected_condition


def keep_bool_preds(formula: Formula, symbol_table):
    if not isinstance(formula, BiOp):
        return (
            formula
            if not any(
                v for v in formula.variablesin() if symbol_table[str(v)] != BOOLEAN
            )
            else true()
        )
    else:
        preds = {
            p
            for p in formula.sub_formulas_up_to_associativity()
            if not any(v for v in p.variablesin() if symbol_table[str(v)] != BOOLEAN)
        }
        return conjunct_formula_set(preds)


def add_prev_suffix(formula):
    # TODO don't create the list each time this is called, cache it in formula
    return append_to_variable_name(formula, [v for v in formula.variablesin()], "_prev")


def transition_up_to_dnf(transition: Transition, symbol_table):
    dnf_condition = dnf(transition.condition, symbol_table)
    if not (isinstance(dnf_condition, BiOp) and dnf_condition.op.startswith("|")):
        return [transition]
    else:
        conds = dnf_condition.sub_formulas_up_to_associativity()
        return [
            Transition(
                transition.src,
                cond,
                transition.action,
                transition.output,
                transition.tgt,
            )
            for cond in conds
        ]


def is_deterministic(program):
    env_state_dict = {s: [] for s in program.states}
    for t in program.transitions:
        env_state_dict.setdefault(t.src, []).append(t.condition)

    symbol_table = program.symbol_table

    for s, conds in env_state_dict.items():
        # O(n) SAT checks instead of O(n^2):
        # if cond_i overlaps with disjunction of previous guards, state is nondeterministic.
        covered = false()
        for cond in conds:
            if sat(conjunct(cond, covered), symbol_table):
                logging.info(
                    "WARNING: transition guard overlap in state "
                    + str(s)
                    + " (non-deterministic), overlapping guard: "
                    + str(cond)
                )
                return False
            covered = disjunct(covered, cond)

    return True


def safe_update_list_vals(d, k, v_arr):
    if k in d.keys():
        d[k] = d[k] + v_arr
    else:
        d[k] = v_arr


def safe_update_set_vals(d, k, v_set):
    if k in d.keys():
        d[k] = d[k] | v_set
    else:
        d[k] = v_set


def safe_update_dict_value(d: dict, k, v_dict):
    if k in d.keys():
        d[k].update(v_dict)
    else:
        d[k] = v_dict


def function_bounded_below_by_0(f: Formula, invars: Formula, symbol_table):
    # TODO, should we conjunct or disjunct invars?

    return not check(
        And(
            *conjunct(conjunct_formula_set(invars), BiOp(f, "<", Value(0))).to_smt(
                symbol_table
            )
        )
    )


def resolve_next_references(transition, valuation):
    condition = transition.condition
    next_vars = [str(v) for v in condition.variablesin() if str(v).endswith("_next")]
    internal_variables = [t.name for t in valuation]
    if len(next_vars) > 0:
        actions = transition.action
        modified_vars = {str(act.left): act.right for act in actions}
        for v in next_vars:
            vanilla_v = v.split("_next")[0]
            if vanilla_v not in internal_variables:
                raise Exception(
                    "Can only use next suffix with internal variables: "
                    + str(transition)
                )
            if vanilla_v in modified_vars.keys():
                condition = condition.replace({Variable(v): modified_vars[vanilla_v]})
            else:
                condition = condition.replace({Variable(v): Variable(vanilla_v)})
        return Transition(
            transition.src,
            condition,
            transition.action,
            transition.output,
            transition.tgt,
        )
    else:
        return transition


def guarded_action_transitions_to_normal_transitions(arg):
    guarded_transition, valuation, env_events, con_events, symbol_table = arg
    if str(guarded_transition.condition) == "otherwise":
        actions = []
        for act, guard in guarded_transition.action:
            guard_formula = (
                true()
                if (guard is None or (isinstance(guard, Value) and guard.is_true()))
                else guard
            )
            if not is_tautology(guard_formula, symbol_table):
                raise Exception("Otherwise transitions cannot have guarded actions")
            actions.append(act)
        return [
            Transition(
                guarded_transition.src,
                guarded_transition.condition,
                actions,
                guarded_transition.output,
                guarded_transition.tgt,
            )
        ]

    symbol_table = {}
    for v in valuation:
        symbol_table[v[0]] = v[1]
        symbol_table[v[0] + "_next"] = v[1]

    for ev, t in env_events + con_events:
        symbol_table[ev.name] = t

    # Group updates by variable while preserving input order.
    updates_by_var = {}
    for act, guard in guarded_transition.action:
        guard_formula = (
            true()
            if (guard is None or (isinstance(guard, Value) and guard.is_true()))
            else guard
        )
        updates_by_var.setdefault(act.left, []).append((act, guard_formula))

    if len(updates_by_var) == 0:
        return [
            Transition(
                guarded_transition.src,
                guarded_transition.condition,
                [],
                guarded_transition.output,
                guarded_transition.tgt,
            )
        ]

    # Build by-order, mutually exclusive cases per variable, then combine
    # satisfiable cases across different variables.
    cases_by_var = {}
    for var, updates in updates_by_var.items():
        seen_guards = []
        guard_buckets = {}

        for act, guard_formula in updates:
            effective_guard = (
                guard_formula
                if len(seen_guards) == 0
                else conjunct(guard_formula, neg(disjunct_formula_set(seen_guards)))
            )
            seen_guards.append(guard_formula)

            if not sat(effective_guard, symbol_table):
                continue

            rhs_key = str(act.right)
            bucket = guard_buckets.setdefault(
                rhs_key, {"act": act, "guards": [], "rhs": act.right}
            )
            bucket["guards"].append(effective_guard)

        var_cases = []
        for bucket in guard_buckets.values():
            merged_guard = disjunct_formula_set(bucket["guards"])
            var_cases.append((bucket["act"], merged_guard))

        # Explicit "no update for this variable" case.
        no_update_guard = neg(disjunct_formula_set(seen_guards))
        if sat(no_update_guard, symbol_table):
            var_cases.append((None, no_update_guard))

        # Sanity: two distinct updates for the same variable must be exclusive.
        for i in range(len(var_cases)):
            act_i, guard_i = var_cases[i]
            if act_i is None:
                continue
            for j in range(i + 1, len(var_cases)):
                act_j, guard_j = var_cases[j]
                if act_j is None:
                    continue
                if sat(conjunct(guard_i, guard_j), symbol_table) and not is_tautology(
                    iff(act_i.right, act_j.right), symbol_table
                ):
                    raise Exception(
                        "Guarded actions are not mutually exclusive: "
                        + str(guard_i)
                        + " and "
                        + str(guard_j)
                        + " for update of variable "
                        + str(var)
                    )

        cases_by_var[var] = var_cases

    combinations = [([], true())]
    ordered_vars = sorted(cases_by_var.keys(), key=lambda v: str(v))
    for var in ordered_vars:
        new_combinations = []
        for current_actions, current_guard in combinations:
            for act, case_guard in cases_by_var[var]:
                combo_guard = conjunct(current_guard, case_guard)
                if not sat(combo_guard, symbol_table):
                    continue
                if act is None:
                    new_actions = list(current_actions)
                else:
                    new_actions = list(current_actions) + [act]
                new_combinations.append((new_actions, combo_guard))
        combinations = new_combinations

    transitions = []
    for actions, action_guard in combinations:
        new_guard = conjunct(guarded_transition.condition, action_guard)
        if not sat(new_guard, symbol_table):
            continue
        transitions.append(
            Transition(
                guarded_transition.src,
                propagate_negations(new_guard),
                actions,
                guarded_transition.output,
                guarded_transition.tgt,
            )
        )

    # Merge transitions with identical action sets by OR-ing their guards.
    merged = {}
    for t in transitions:
        action_sig = tuple(sorted((str(a.left), str(a.right)) for a in t.action))
        entry = merged.setdefault(
            action_sig,
            {
                "actions": sorted(t.action, key=lambda a: str(a.left)),
                "guards": [],
            },
        )
        entry["guards"].append(t.condition)

    transitions = [
        Transition(
            guarded_transition.src,
            propagate_negations(disjunct_formula_set(entry["guards"])),
            entry["actions"],
            guarded_transition.output,
            guarded_transition.tgt,
        )
        for entry in merged.values()
    ]

    # debug
    if config.Config.getConfig().debug:
        collect_guards = []
        for t in transitions:
            collect_guards += [t.condition]
        if sat(
            (
                conjunct(
                    guarded_transition.condition,
                    neg(disjunct_formula_set(collect_guards)),
                )
            ),
            symbol_table,
        ):
            raise Exception("Not all transitions are covered by guards")

    return transitions


transition_formulas = {}


def transition_formula(t):
    if t not in transition_formulas.keys():
        formula = conjunct(
            add_prev_suffix(t.condition),
            conjunct_formula_set(
                [
                    BiOp(act.left, "=", add_prev_suffix(act.right))
                    for act in t.action
                    if not isinstance(act.right, NonDeterministic)
                ]
            ),
        )
        transition_formulas[t] = formula
        return formula
    else:
        return transition_formulas[t]


def issy_transition_formula(t, states_in_spec):
    to_return = f"from {t.src} to {t.tgt} with "
    cond = str(t.condition)
    preds = atomic_predicates(t.condition)
    to_replace = {str(p): f"[{str(p)}]" for p in preds}
    for k, v in to_replace.items():
        cond = re.sub(rf"\b{k}\b", v, cond)

    stutters = [u.left for u in t.action if u.left == u.right]
    if len(stutters) > 0:
        cond += f" && keep({' '.join([str(s) for s in stutters])})"
    updates = [u for u in t.action if u.left != u.right]
    for u in updates:
        cond += f" && [{str(u.left)}' = {str(u.right)}]"
    for s in states_in_spec:
        if s == t.tgt:
            cond += f" && [{s}' = true]"
        else:
            cond += f" && [{s}' = false]"

    to_return += cond
    return to_return


guard_update_formulas = {}
guard_formulas_unpacked = {}


def guard_update_formula(g, u, symbol_table):
    key = pickle.dumps((g, u))
    if key not in transition_formulas.keys():
        formula = conjunct(
            add_prev_suffix(g),
            conjunct_formula_set(
                [BiOp(act.left, "=", add_prev_suffix(act.right)) for act in u]
            ),
        )
        guard_update_formulas[key] = formula
        guard_formulas_unpacked[formula] = (g, u)
        return formula
    else:
        return guard_update_formulas[key]


def guard_update_formula_to_guard_update(gu):
    if gu in guard_formulas_unpacked.keys():
        return guard_formulas_unpacked[gu]
    else:
        raise Exception(
            "programs.util: "
            + str(gu)
            + " not in guard_update_formulasguard_update_formulas"
        )


def powerset_complete(SS: iterable):
    if not isinstance(SS, set):
        S = set(SS)
    else:
        S = SS
    positive_subsets = chain.from_iterable(
        combinations(S, r) for r in range(len(S) + 1)
    )
    complete_subsets = list()

    for ps in positive_subsets:
        real_ps = set(ps)
        negative = {neg(s) for s in S if (s) not in real_ps}
        complete = set(real_ps).union(negative)
        complete_subsets.append(frozenset(complete))

    return complete_subsets


def complete_powerset(arg):
    S, ps = arg
    real_ps = set(ps)
    negative = {neg(s) for s in S if (s) not in real_ps}
    return frozenset(set(real_ps).union(negative))


powersets = {}


def powerset(S: set):
    if frozenset(S) in powersets.keys():
        return powersets[frozenset(S)]
    else:
        subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
        subsets = sorted(list(map(set, subsets)), key=lambda x: len(x))

        powersets[frozenset(S)] = subsets
        return subsets


def binary_rep_states(
    vars, printing=True, log=True, collect_to=None, force_table=False
):
    return binary_rep(
        vars,
        "bin_st_",
        printing=printing,
        log=log,
        collect_to=collect_to,
        force_table=force_table,
    )


def binary_rep(
    vars,
    label,
    printing=True,
    log=True,
    collect_to=None,
    force_table=False,
):
    bin_vars, rep = BinaryRepMap.build_binary_rep(vars, label)

    should_emit = force_table or rep.should_emit_table(label)
    if should_emit:
        mapping_table = rep.format_table(label)
        if log:
            logging.info(mapping_table)
        if printing:
            print(mapping_table)

        if collect_to is not None and hasattr(collect_to, "register_binary_rep_table"):
            collect_to.register_binary_rep_table(label, mapping_table)

    return bin_vars, rep


def term_incremented_or_decremented(program, f):
    vars_in_f = f.variablesin()
    # prev_vars = [Variable(v.name + "_prev") for v in vars_in_f]
    # vars_in_f.extend(prev_vars)

    only_updated_by_constants = True
    only_updated_by_other_program_vars = True

    there_is_inc = False
    there_is_dec = False
    there_is_inc_dec_in_same_scc = False
    for scc in program.sccs:
        scc_inc = False
        scc_dec = False
        updates = {u for t in scc for u in t.action}
        for u in updates:
            if u.left in vars_in_f:
                if u.left == u.right:
                    continue
                else:
                    dec = BiOp(add_prev_suffix(f), ">", f)
                    inc = BiOp(add_prev_suffix(f), "<", f)
                    act = BiOp(u.left, "==", add_prev_suffix(u.right))
                    dec_here = sat(conjunct(dec, act), program.symbol_table)
                    inc_here = sat(conjunct(inc, act), program.symbol_table)

                    scc_inc = True if inc_here else scc_inc
                    scc_dec = True if dec_here else scc_dec

                    vars_in_u = u.right.variablesin()
                    if len(vars_in_u) > 0:
                        only_updated_by_constants = False
                    # if a variable v only depends on other program variables
                    # then the predicate abstraction will implicitly force v to progress towards
                    # the ends of the partition (if the other variables are forced to do so)
                    # so only need a ranking refinement for v if it depends on itself, or on inputs
                    # prev_vars = [Variable(v.name + "_prev") for v in vars_in_u]
                    # vars_in_u.extend(prev_vars)
                    if u.left in vars_in_u or any(
                        v for v in vars_in_u if v in program.num_in_out
                    ):
                        only_updated_by_other_program_vars = False
        if scc_inc:
            there_is_inc = True
            if scc_dec:
                there_is_dec = True
                there_is_inc_dec_in_same_scc = True
        elif scc_dec:
            there_is_dec = True

    return (
        only_updated_by_constants,
        only_updated_by_other_program_vars,
        there_is_dec,
        there_is_inc,
        there_is_inc_dec_in_same_scc,
    )


def reset_caches():
    stutter_transition_cache.clear()
    transition_formulas.clear()

    guard_update_formulas.clear()

    guard_formulas_unpacked.clear()

    powersets.clear()


def refine_init_values(
    program,
    initial_assumptions,
    *,
    use_ltl_horizon: bool = False,
    bad_states=None,
):
    if use_ltl_horizon:
        _, vars_init_val_no_matter = classify_initial_values_with_ltl_horizon(
            program,
            initial_assumptions,
            bad_states=bad_states,
        )
        vars_blocked_by_objective_occurrence = set()
    else:
        _, vars_init_val_no_matter = classify_initial_values(program)
        preds = atomic_predicates(initial_assumptions)
        vars_blocked_by_objective_occurrence = set(
            itertools.chain.from_iterable([p.variablesin() for p in preds])
        )

    for v in vars_init_val_no_matter:
        if v in vars_blocked_by_objective_occurrence:
            continue
        if program.symbol_table[str(v)] == BOOLEAN:
            program.init_var_values[str(v)] = Value(BoolAtoms.FALSE)
            program.unset_init_vars.remove(str(v))
        else:
            program.init_var_values[str(v)] = Value(0)
            program.unset_init_vars.remove(str(v))

    return program
