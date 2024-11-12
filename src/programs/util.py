import logging
import math
import os
import pickle
import re
import shutil
import time
from itertools import chain, combinations

from pysmt.factory import SolverRedefinitionError
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import get_env, And
from sympy.utilities.iterables import iterable

from analysis.smt_checker import check, bdd_simplify
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, conjunct, neg, append_to_variable_name, dnf, disjunct_formula_set, \
    true, sat, is_tautology, iff, propagate_negations, type_constraints, cnf_safe, var_to_predicate, fnode_to_formula, \
    run_with_timeout, simplify_formula_with_math
from prop_lang.value import Value
from prop_lang.variable import Variable


def symbol_table_from_program(program):
    symbol_table = dict()
    for state in program.states:
        symbol_table[state] = TypedValuation(str(state), "bool", None)
    for ev in program.out_events + program.env_events + program.con_events:
        symbol_table[ev.name] = TypedValuation(str(ev), "bool", None)
    for t_val in program.valuation:
        symbol_table[t_val.name] = t_val
        symbol_table[t_val.name + "_prev"] = TypedValuation(t_val.name + "_prev", t_val.type, None)
        symbol_table[t_val.name + "_prev" + "_prev"] = TypedValuation(t_val.name + "_prev" + "_prev", t_val.type, None)
    return symbol_table


def symbol_table_from_typed_valuation(tv):
    symbol_table = dict()
    for t_val in tv:
        symbol_table[t_val.name] = t_val
    return symbol_table


def ce_state_to_predicate_abstraction_trans(ltl_to_program_transitions, symbol_table, start, middle, end,
                                            env_events, con_events):
    # ltl_to_program_transitions is a dict of the form {now: {(con_ev, env_ev) : [(con_trans, env_trans)]}}
    start = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in start.items() if
                                  (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                      key) in env_events + con_events) and value == "TRUE"]
                                 + [neg(Variable(key.removeprefix("mon_"))) for key, value in start.items() if
                                    (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                        key) in env_events + con_events) and value == "FALSE"])
    middle = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in middle.items() if
                                   (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                       key) in env_events + con_events) and value == "TRUE"]
                                  + [neg(Variable(key.removeprefix("mon_"))) for key, value in middle.items() if
                                     (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                         key) in env_events + con_events) and value == "FALSE"])
    end = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in end.items() if
                                (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                    key) in env_events + con_events) and value == "TRUE"]
                               + [neg(Variable(key.removeprefix("mon_"))) for key, value in end.items() if
                                  (key.startswith("mon_") or key.startswith("pred_") or Variable(
                                      key) in env_events + con_events) and value == "FALSE"])

    for abs_con_start in ltl_to_program_transitions.keys():
        if abs_con_start == "init":
            continue
        if check(And(*(conjunct(abs_con_start, start).to_smt(symbol_table)))):
            for (abs_env_start, abs_env_end) in ltl_to_program_transitions[abs_con_start].keys():
                if check(And(*(conjunct(abs_env_start, middle).to_smt(symbol_table)))):
                    if check(And(*(conjunct(abs_env_end, end).to_smt(symbol_table)))):
                        return ltl_to_program_transitions[abs_con_start][(abs_env_start, abs_env_end)]

    return []


def check_for_nondeterminism_last_step(state_before_mismatch, program, raise_exception=False, exception=None):
    transitions = program.transitions + program.con_transitions

    guards = []
    for (key, value) in state_before_mismatch.items():
        if key.startswith("guard_") and value == "TRUE" and len(transitions) != int(key.replace("guard_", "")):
            guards.append(looping_to_normal(transitions[int(key.replace("guard_", ""))]))

    if len(guards) > 1:
        message = ("Nondeterminism in last step of counterexample; program has choice between: \n"
                   + "\n".join([str(t) for t in guards])
                   + "\nWe do not handle this yet."
                   + "\nIf you suspect the problem to be realisabile, "
                   + "give control to the environment of the transitions (e.g., with a new variable).\n"
                   + "Otherwise, if you suspect unrealisability, give control of the transitions to the controller.")
        if raise_exception:
            if exception == None:
                raise Exception(message)
            else:
                raise Exception(message) from exception
        else:
            logging.info("WARNING: " + message)


def parse_nuxmv_ce_output_finite(program, out, cs_alphabet):
    prefix, _ = get_ce_from_nuxmv_output(out)

    agreed_on_transitions, incompatible_state = prog_transition_indices_and_state_from_ce(program, prefix, cs_alphabet)

    return agreed_on_transitions, incompatible_state


def prog_transition_indices_and_state_from_ce(program, prefix, cs_alphabet):
    transition_no = len(program.transitions)
    program_alphabet = [str(s) for s in program.states] + [tv.name for tv in program.valuation]
    program_states = []
    program_transitions = []
    cs_states = []

    for dic in prefix:
        # monitor only makes decisions at env and mon turns
        if dic["turn"] == "cs":
            transition = "-1"
            program_state = {}
            cs_state = {}
            for (key, value) in dic.items():
                if key.split("_prev")[0] in program_alphabet:
                    program_state[key] = value
                elif key in cs_alphabet or key.startswith("compatible") or key.startswith("pred"):
                    cs_state[key] = value
                elif key.startswith("guard_") and value == "TRUE":
                    if dic[key.replace("guard_", "act_")] == "TRUE":
                        no = key.replace("guard_", "")
                        if no != str(transition_no):
                            transition = no

            program_states.append(program_state)
            cs_states.append(cs_state)
            program_transitions.append(transition)

    return (program_transitions[:-1], program_states[:-1], cs_states[:-1]), (program_transitions[-1], program_states[-1], cs_states[-1])


def get_ce_from_nuxmv_output(out: str):
    ce = out.split("Counterexample")[1].strip()
    # ce = re.sub("[^\n]*(act|guard)\_[0-9]+ = [^\n]+", "", ce)
    ce = re.sub("[^\n]*(identity)_[^\n]+", "", ce)

    prefix = ce

    prefix = re.split("[^\n]*\->[^<]*<\-", prefix)
    prefix = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in prefix]
    prefix.remove([])
    prefix = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t]) for t in prefix]

    loop = []

    complete_prefix, complete_loop = complete_ce(prefix, loop)

    prune_up_to_mismatch = []
    for i in range(0, len(complete_prefix)):
        if complete_prefix[i]["compatible"] == "TRUE":
            prune_up_to_mismatch += [complete_prefix[i]]
        else:
            prune_up_to_mismatch += [complete_prefix[i]]  # add mismatching state
            break
    return prune_up_to_mismatch, complete_prefix[len(prune_up_to_mismatch):] + complete_loop


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        complete_ce_state(prefix[i - 1], prefix[i])

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
    return [key for key in state1.keys() if key in state2.keys() and state1[key] != state2[key]]


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
        to_replace_with.append(BiOp(Variable(key + "_" + str(i)), ":=", Value(value)))
    return formula.replace(to_replace_with)


def reduce_up_to_iff(old_preds, new_preds, symbol_table, tautology_check=True):
    if len(new_preds) == 0:
        return old_preds

    keep_these = set()
    remove_these = set()

    for p in set(new_preds):
        if p and neg(p) not in remove_these and \
            not isinstance(p, Value) and not isinstance(neg(p), Value) and \
                not has_equiv_pred(p, set(old_preds) | keep_these, symbol_table) and \
                (not tautology_check or not (is_tautology(p, symbol_table) or is_tautology(neg(p), symbol_table))):
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
        if is_tautology(iff(p, pp), symbol_table) or \
                is_tautology(iff(neg(p), pp), symbol_table):
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
    fnode = And(*guard.to_smt(program.symbol_table))
    order = [v for v in fnode.get_free_variables() if Variable(str(v)) in program.env_events + program.con_events]
    condition_simplified = bdd_simplify(fnode, static_ordering=order)
    if condition_simplified is not None:
        condition_simplified = fnode_to_formula(condition_simplified)
        print("simplified " + str(guard) + " (len " + str(len(guard)) + ") to " + str(condition_simplified) + " (len " + str(len(condition_simplified)) + ")")
        return condition_simplified
    else:
        return guard


def stutter_transition(program, state, cnf=False):
    transitions = program.transitions
    condition = neg(disjunct_formula_set([t.condition
                                          for t in transitions if t.src == state]))
    
    if program not in stutter_transition_cache.keys():
        stutter_transition_cache[program] = {}

    if condition in stutter_transition_cache.keys():
        return stutter_transition_cache[program][condition]

    cond_fnode = And(*condition.to_smt(program.symbol_table))

    if check(cond_fnode):
        if cnf:
            # conf = config.Config.getConfig()
            # start = time.time()
            # if conf.cnf_optimisations:
            #     condition_simplified = cnf_safe(condition, program.symbol_table, timeout=2)
            # else:
            args = [program, condition]
            success, condition_simplified = run_with_timeout(bdd_simplify_guards, args, timeout=0.2)
            # if condition_simplified != condition:
            #     logging.info("CNFing stutter transition " + str(condition) + " took " + str(time.time() - start) + " seconds.\n" +
            #              "With result " + str(condition_simplified))
            # else:
            #     logging.info("Took too long to CNF stutter transition " + str(condition) + ", took" + str(time.time() - start) + " seconds.")
            if success:
                condition = condition_simplified
        stutter_t = Transition(state,
                               condition,
                               [],
                               [],
                               state).complete_outputs(program.out_events) \
            .complete_action_set([Variable(v.name) for v in program.valuation])
        stutter_transition_cache[program][condition] = stutter_t
        return stutter_t
    else:
        stutter_transition_cache[program][condition] = None
        return None


def looping_to_normal(t: Transition):
    return t  # Transition(re.split("_loop", t.src)[0], t.condition, t.action, t.output,  re.split("_loop", t.tgt)[0]) \
    #  if "loop" in ((t.src) + (t.tgt)) else t


def preds_in_state(ce_state: dict[str, str]):
    return [var_to_predicate(Variable(p)) for p, v in ce_state.items() if p.startswith("pred_") and v == "TRUE"] \
        + [neg(var_to_predicate((Variable(p)))) for p, v in ce_state.items() if
           p.startswith("pred_") and v == "FALSE"]


def ground_transitions(program, transition_and_state_list, vars_to_ground_on, symbol_table):
    grounded = []
    for (t, st) in transition_and_state_list:
        projected_condition = ground_predicate_on_vars(program, t.condition, st, vars_to_ground_on, symbol_table)
        grounded += [Transition(t.src,
                                projected_condition,
                                [a for a in t.action if str(a.left) not in vars_to_ground_on],
                                t.output,
                                t.tgt)]
    return grounded


def ground_predicate_on_vars(program, predicate, ce_state, vars, symbol_table):
    grounded_state = project_ce_state_onto_ev(ce_state,
                                              program.env_events + program.con_events + program.out_events
                                              + [Variable(str(v)) for v in vars])
    projected_condition = predicate.replace(
        [BiOp(Variable(key), ":=", Value(grounded_state[key])) for key in grounded_state.keys()])
    return projected_condition


def keep_bool_preds(formula: Formula, symbol_table):
    if not isinstance(formula, BiOp):
        return formula if not any(v for v in formula.variablesin() if symbol_table[str(v)].type != "bool") else true()
    else:
        preds = {p for p in formula.sub_formulas_up_to_associativity() if
                 not any(v for v in p.variablesin() if symbol_table[str(v)].type != "bool")}
        return conjunct_formula_set(preds)


def add_prev_suffix(formula):
    return append_to_variable_name(formula, [str(v) for v in formula.variablesin()], "_prev")


def transition_up_to_dnf(transition: Transition, symbol_table):
    dnf_condition = dnf(transition.condition, symbol_table)
    if not (isinstance(dnf_condition, BiOp) and dnf_condition.op.startswith("|")):
        return [transition]
    else:
        conds = dnf_condition.sub_formulas_up_to_associativity()
        return [Transition(transition.src, cond, transition.action, transition.output, transition.tgt) for cond in
                conds]


def is_deterministic(program):
    env_state_dict = {s: [t.condition for t in program.transitions if t.src == s] for s in program.states}

    symbol_table = program.symbol_table

    for (s, conds) in env_state_dict.items():
        # Assuming satisfiability already checked
        sat_conds = [cond for cond in conds]

        for i, cond in enumerate(sat_conds):
            for cond2 in sat_conds[i + 1:]:
                if check(And(*(cond.to_smt(symbol_table) + cond2.to_smt(symbol_table)))):
                    logging.info("WARNING: " + str(cond) + " and " + str(
                        cond2) + " are satisfiable together, see environment transitions from state " + str(s))
                    return False

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
        And(*conjunct(conjunct_formula_set(invars), BiOp(f, "<", Value(0))).to_smt(symbol_table)))


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
                raise Exception("Can only use next suffix with internal variables: " + str(transition))
            if vanilla_v in modified_vars.keys():
                condition = condition.replace([BiOp(Variable(v), ":=", modified_vars[vanilla_v])])
            else:
                condition = condition.replace([BiOp(Variable(v), ":=", Variable(vanilla_v))])
        return Transition(transition.src, condition, transition.action, transition.output, transition.tgt)
    else:
        return transition


def guarded_action_transitions_to_normal_transitions(arg):
    guarded_transition, valuation, env_events, con_events, symbol_table = arg
    if str(guarded_transition.condition) == "otherwise":
        # check that no guarded actions
        for (act, guard) in guarded_transition.action:
            if guard is not None or str(guard) != "true":
                raise Exception("Otherwise transitions cannot have guarded actions")
        return [guarded_transition]

    unguarded_acts = []
    guarded_acts = {act: set() for (act, _) in guarded_transition.action}
    for (act, guard) in guarded_transition.action:
        if isinstance(guard, Value):
            if guard.is_true():
                unguarded_acts += [act]
        else:
            new_guard = conjunct(guard, type_constraints(act.left, symbol_table))
            guarded_acts[act].add(new_guard)

    guarded_acts = {act: g_set for act, g_set in guarded_acts.items() if len(g_set) > 0}

    if len(guarded_acts) == 0:
        return [
            Transition(guarded_transition.src, guarded_transition.condition, unguarded_acts, guarded_transition.output,
                       guarded_transition.tgt)]

    transitions = []

    symbol_table = {}
    for t_val in valuation:
        symbol_table[t_val.name] = t_val
        symbol_table[t_val.name + "_next"] = TypedValuation(t_val.name + "_next", t_val.type, t_val.value)

    for ev in env_events + con_events:
        symbol_table[ev.name] = TypedValuation(str(ev), "bool", None)

    act_guard_sets = set()
    act_guard_sets.add(frozenset({}))
    for act in guarded_acts.keys():
        new_act_guard_sets = set()
        # check that each guard is mutually exclusive with the other guards
        for guard1 in guarded_acts[act]:
            for guard2 in guarded_acts[act]:
                if guard1 != guard2 and sat(conjunct(guard1, guard2), symbol_table):
                    raise Exception("Guarded actions are not mutually exclusive: " + str(guard1) + " and " + str(
                        guard2) + " in " + str(guarded_transition))
            for act_guard_set in act_guard_sets:
                guard1true = frozenset(act_guard_set | {(act, guard1)})
                guard1false = frozenset(act_guard_set | {(None, neg(guard1))})
                if sat(conjunct_formula_set([g for (_, g) in guard1true]), symbol_table):
                    new_act_guard_sets.add(guard1true)
                if sat(conjunct_formula_set([g for (_, g) in guard1false]), symbol_table):
                    new_act_guard_sets.add(guard1false)
        act_guard_sets = new_act_guard_sets

    for act_guard_set in act_guard_sets:
        action_guards = conjunct_formula_set(
            sorted(list({guard for (_, guard) in act_guard_set}), key=lambda x: str(x)))
        new_guard = conjunct(guarded_transition.condition, action_guards)
        if not sat(new_guard, symbol_table):
            continue

        actions = [act for (act, _) in act_guard_set if act != None]

        transitions.append(Transition(guarded_transition.src, propagate_negations(new_guard),
                                      unguarded_acts + actions, guarded_transition.output, guarded_transition.tgt))

    # debug
    collect_guards = []
    for t in transitions:
        collect_guards += [t.condition]
    if sat((conjunct(guarded_transition.condition, neg(disjunct_formula_set(collect_guards)))), symbol_table):
        raise Exception("Not all transitions are covered by guards")
    return transitions


transition_formulas = {}


def transition_formula(t):
    if t not in transition_formulas.keys():
        formula = conjunct(add_prev_suffix(t.condition),
                           conjunct_formula_set([BiOp(act.left, "=", add_prev_suffix(act.right)) for act in
                                                 t.action]))
        transition_formulas[t] = formula
        return formula
    else:
        return transition_formulas[t]


guard_update_formulas = {}
guard_formulas_unpacked = {}

def guard_update_formula(g, u, symbol_table):
    key = pickle.dumps((g,u))
    if key not in transition_formulas.keys():
        formula = conjunct(add_prev_suffix(g),
                           conjunct_formula_set([BiOp(act.left, "=", add_prev_suffix(act.right))
                                                 for act in u]))
        guard_update_formulas[key] = formula
        guard_formulas_unpacked[formula] = (g,u)
        return formula
    else:
        return guard_update_formulas[key]


def guard_update_formula_to_guard_update(gu):
    if gu in guard_formulas_unpacked.keys():
        return guard_formulas_unpacked[gu]
    else:
        raise Exception("programs.util: " + str(gu) + " not in guard_update_formulasguard_update_formulas")



def powerset_complete(SS: iterable):
    if not isinstance(SS, set):
        S = set(SS)
    else:
        S = SS
    positive_subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
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


def binary_rep_states(vars):
    return binary_rep(vars, "bin_st_")


def binary_rep(vars, label):
    if len(vars) == 0:
        raise Exception("Cannot create binary representation of empty set")

    bin = math.log(len(vars), 2)
    bin = math.ceil(bin)
    if bin == 0:
        bin = 1

    bin_vars = [Variable(label + str(i)) for i in range(0, bin)]

    base = '{0:0' + str(bin) + 'b}'
    rep = {}
    for i, v in enumerate(vars):
        bin_rep = base.format(i)
        bin_formula = None
        for j, pos in enumerate(bin_rep):
            if pos == '0':
                new_constraint = neg(bin_vars[j])
            else:
                new_constraint = bin_vars[j]

            if bin_formula is None:
                bin_formula = new_constraint
            else:
                bin_formula = conjunct(bin_formula, new_constraint)
        rep[v] = bin_formula

    for v, f in rep.items():
        if isinstance(v, frozenset):
            print("state: " + str(conjunct_formula_set(v)))
        else:
            print("state: " + str(v))
        print("binary rep: " + str(f))
    return bin_vars, rep


def term_incremented_or_decremented(program, f):
    updates = [u for trans in program.transitions for u in trans.action]
    vars_in_f = f.variablesin()

    only_updated_by_constants = True

    there_is_inc = False
    there_is_dec = False
    for u in set(updates):
        if u.left in vars_in_f:
            if u.left == u.right:
                continue
            else:
                dec = BiOp(add_prev_suffix(f), ">", f)
                inc = BiOp(add_prev_suffix(f), "<", f)
                act = BiOp(u.left, "==", add_prev_suffix(u.right))
                if sat(conjunct(dec, act), program.symbol_table):
                    there_is_dec = True
                    if len(u.right.variablesin()) > 0:
                        only_updated_by_constants = False
                if sat(conjunct(inc, act), program.symbol_table):
                    there_is_inc = True
                    if len(u.right.variablesin()) > 0:
                        only_updated_by_constants = False

                if there_is_dec and there_is_inc and not only_updated_by_constants:
                    break

    return only_updated_by_constants, there_is_dec, there_is_inc
