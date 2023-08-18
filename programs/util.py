import os
import re
import shutil
from itertools import chain, combinations

from pysmt.factory import SolverRedefinitionError
from pysmt.fnode import FNode
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import get_env, And

from programs.analysis.model_checker import ModelChecker
from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, conjunct, neg, append_to_variable_name, dnf, disjunct_formula_set, \
    true, sat, is_tautology, iff, propagate_negations, type_constraints
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
    return symbol_table


def symbol_table_from_typed_valuation(tv):
    symbol_table = dict()
    for t_val in tv:
        symbol_table[t_val.name] = t_val
    return symbol_table


def ce_state_to_predicate_abstraction_trans(ltl_to_program_transitions, symbol_table, start, middle, end,
                                            env_events, con_events):
    # ltl_to_program_transitions is a dict of the form {now: {(con_ev, env_ev) : [(con_trans, env_trans)]}}
    smt_checker = SMTChecker()

    start = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in start.items() if
                                      (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "TRUE"]
                                     + [neg(Variable(key.removeprefix("mon_"))) for key, value in start.items() if
                                        (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "FALSE"])
    middle = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in middle.items() if
                                    (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "TRUE"]
                                   + [neg(Variable(key.removeprefix("mon_"))) for key, value in middle.items() if
                                      (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "FALSE"])
    end = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in end.items() if
                                    (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "TRUE"]
                                   + [neg(Variable(key.removeprefix("mon_"))) for key, value in end.items() if
                                      (key.startswith("mon_") or key.startswith("pred_") or Variable(key) in env_events + con_events) and value == "FALSE"])

    for abs_con_start in ltl_to_program_transitions.keys():
        if abs_con_start == "init":
            continue
        if smt_checker.check(And(*(conjunct(abs_con_start, start).to_smt(symbol_table)))):
            for (abs_env_start, abs_env_end) in ltl_to_program_transitions[abs_con_start].keys():
                if smt_checker.check(And(*(conjunct(abs_env_start, middle).to_smt(symbol_table)))):
                    if smt_checker.check(And(*(conjunct(abs_env_end, end).to_smt(symbol_table)))):
                        return ltl_to_program_transitions[abs_con_start][(abs_env_start, abs_env_end)]

    return []


def check_for_nondeterminism_last_step(state_before_mismatch, program, raise_exception=False, exception=None):
    transitions = program.env_transitions + program.con_transitions

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
            print("WARNING: " + message)


def parse_nuxmv_ce_output_finite(transition_no, out: str):
    prefix, _ = get_ce_from_nuxmv_output(out)

    tran_indices, incompatible_state = prog_transition_indices_and_state_from_ce(transition_no, prefix)

    return prefix, tran_indices, incompatible_state


def prog_transition_indices_and_state_from_ce(transition_no, prefix):
    program_transitions_and_state = []

    for dic in prefix:
        # monitor only makes decisions at env and mon turns
        if dic["turn"] == "env" or dic["turn"] == "con":
            transition = "-1"
            for (key, value) in dic.items():
                if key.startswith("guard_") and value == "TRUE":
                    if dic[key.replace("guard_", "act_")] == "TRUE":
                        no = key.replace("guard_", "")
                        if no != str(transition_no):
                            transition = no
                        break
            state = {key: value for key, value in dic.items()}
            # dic_without_prev_vars = {key: value for key, value in dic.items() if not key.endswith("_prev")}
            program_transitions_and_state.append((transition, state))

    incompatibility_detetected_at_turn = prefix[-1]["turn"]
    if incompatibility_detetected_at_turn != "env" or incompatibility_detetected_at_turn != "con":
        return program_transitions_and_state, prefix[-1]
    else:
        return program_transitions_and_state, None


def get_ce_from_nuxmv_output(out: str):
    ce = out.split("Counterexample")[1].strip()
    # ce = re.sub("[^\n]*(act|guard)\_[0-9]+ = [^\n]+", "", ce)
    ce = re.sub("[^\n]*(identity)_[^\n]+", "", ce)
    prefix_and_loop = re.split("-- Loop starts here", ce)
    prefix = prefix_and_loop[0].strip()
    loop = prefix_and_loop[1].strip()

    prefix = re.split("[^\n]*\->[^<]*<\-", prefix)
    prefix = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in prefix]
    prefix.remove([])
    prefix = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t]) for t in prefix]

    loop = re.split("[^\n]*\->[^<]*<\-", loop.strip())
    loop = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in loop]
    loop.remove([])
    loop = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t if len(s.strip()) > 0]) for t in loop]

    complete_prefix, complete_loop = complete_ce(prefix, loop)

    prune_up_to_mismatch = []
    for i in range(0, len(complete_prefix)):
        if complete_prefix[i]["compatible"] == "TRUE":
            prune_up_to_mismatch += [complete_prefix[i]]
        else:
            prune_up_to_mismatch += [complete_prefix[i]] # add mismatching state
            break
    return prune_up_to_mismatch, complete_prefix[len(prune_up_to_mismatch):] + complete_loop


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        complete_ce_state(prefix[i - 1], prefix[i])

    complete_ce_state(prefix[len(prefix) - 1], loop[0])
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
    return [key for key in state1.keys() if key in state2.keys() and state1[key] != state2[key]]


def fnode_to_formula(fnode: FNode) -> Formula:
    if fnode.is_constant():
        return Value(fnode.constant_value())
    elif fnode.is_symbol():
        return Variable(fnode.symbol_name())
    else:
        args = [fnode_to_formula(x) for x in fnode.args()]
        if fnode.is_le():
            return MathExpr(BiOp(args[0], "<=", args[1]))
        elif fnode.is_lt():
            return MathExpr(BiOp(args[0], "<", args[1]))
        elif fnode.is_plus():
            return MathExpr(BiOp(args[0], "+", args[1]))
        elif fnode.is_minus():
            return MathExpr(BiOp(args[0], "-", args[1]))
        elif fnode.is_div():
            return MathExpr(BiOp(args[0], "/", args[1]))
        elif fnode.is_times():
            return MathExpr(BiOp(args[0], "*", args[1]))
        elif fnode.is_not():
            return UniOp("!", args[0])
        else:
            if fnode.is_equals():
                op = "="
            elif fnode.is_and():
                op = "&"
            elif fnode.is_or():
                op = "|"
            elif fnode.is_implies():
                op = "<->"
            elif fnode.is_iff():
                op = "<->"
            else:
                raise NotImplementedError(str(fnode) + " cannot be represented as a Formula.")

            if len(args) < 2:
                raise Exception("Expected equality to have more that 1 sub-formula.")

            formula = BiOp(args[0], op, args[1])
            for i in range(2, len(args)):
                formula = conjunct(formula, BiOp(args[i - 1], op, args[i]))
            return formula


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


def label_pred(p, preds):
    if p not in preds:
        return stringify_pred_take_out_neg(p)
    else:
        return stringify_pred(p)


def stringify_pred(p):
    return Variable("pred_" +
                    str(p)
                    .replace(" ", "")
                    .replace("_", "")
                    .replace("(", "_")
                    .replace(")", "_")
                    .replace("=", "_EQ_")
                    .replace(">", "_GT_")
                    .replace("<=", "_LTEQ_")
                    .replace("<", "_LT_")
                    .replace(">=", "_GTEQ_")
                    .replace("-", "_MINUS_")
                    .replace("+", "_PLUS_")
                    .replace("/", "_DIV_")
                    .replace("*", "_MULT_")
                    .replace("%", "_MOD_")
                    .replace("!", "_NEG_")
                    .replace("&&", "_AND_")
                    .replace("&", "_AND_")
                    .replace("||", "_OR_")
                    .replace("|", "_OR_")
                    .replace("->", "_IMPLIES_")
                    .replace("=>", "_IMPLIES_")
                    .replace("<->", "_IFF_")
                    .replace("<=>", "_IFF_")
                    )

def stringify_pred_take_out_neg(p):
    res = None
    if (isinstance(p, UniOp) and p.op == "!"):
        res = neg(stringify_pred(p.right))
    else:
        res = stringify_pred(p)
    if res == None:
        raise Exception("Could not stringify predicate: " + str(p))
    else:
        return res


def label_preds(ps, preds):
    return {label_pred(p, preds) for p in ps}

def reduce_up_to_iff(old_preds, new_preds, symbol_table):
    if len(new_preds) == 0:
        return old_preds
    # if len(old_preds) == 0:
    #     return new_preds
    smt_checker = SMTChecker()

    keep_these = set()
    remove_these = set()

    for p in set(new_preds):
        if p and neg(p) not in remove_these and \
                not has_equiv_pred(p, set(old_preds) | keep_these, symbol_table) and \
                not (is_tautology(p, symbol_table, smt_checker) or is_tautology(neg(p), symbol_table, smt_checker)):
            keep_these.add(p)
        else:
            remove_these.add(p)
            remove_these.add(neg(p))

    return keep_these | set(old_preds)


def has_equiv_pred(p, preds, symbol_table):
    if p in preds or neg(p) in preds:
        return True
    smt_checker = SMTChecker()

    for pp in preds:
        #technically should check if it can be expressed using a set of the existing predicates, but can be expensive
        if is_tautology(iff(p, pp), symbol_table, smt_checker) or \
                is_tautology(iff(neg(p), pp), symbol_table, smt_checker):
            return True

    return False


def project_ce_state_onto_ev(state: dict, events):
    return {k: v for k, v in state.items() if Variable(k) in events}


def synthesis_problem_to_TLSF_script(inputs, outputs, assumptions, guarantees):
    info = "INFO {\n" + \
           '\tTITLE:       ""\n' + \
           '\tDESCRIPTION: ""\n' + \
           "\tSEMANTICS:   Mealy\n" + \
           "\tTARGET:      Mealy\n" + \
           "}\n"

    main = "MAIN {\n"
    main += "\tINPUTS { \n\t\t"
    main += ";\n\t\t".join(map(str, inputs))
    main += "\n\t}\n"
    main += "\tOUTPUTS { \n\t\t"
    main += ";\n\t\t".join(map(str, outputs))
    main += "\n\t}\n"
    main += "\tASSUMPTIONS {\n\t\t"
    main += ";\n\n\t\t".join(map(str, assumptions))
    main += "\n\t}\n"
    main += "\tGUARANTEES { \n\t\t"
    main += ";\n\n\t\t".join(map(str, guarantees))
    main += "\n\t}\n"
    main += "}"

    return info + main


def stutter_transitions(program, env: bool):
    stutter_transitions = []
    for state in program.states:
        st = stutter_transition(program, state, env)
        if st != None:
            stutter_transitions.append(st)
    return stutter_transitions


def stutter_transition(program, state, env: bool):
    transitions = program.env_transitions if env else program.con_transitions
    condition = neg(disjunct_formula_set([t.condition
                                      for t in transitions if t.src == state]))
    smt_checker = SMTChecker()

    if smt_checker.check(And(*condition.to_smt(program.symbol_table))):
        return Transition(state,
                          condition,
                          [],
                          [],
                          state).complete_outputs(program.out_events)\
            .complete_action_set([Variable(v.name) for v in program.valuation])
    else:
        return None

def looping_to_normal(t : Transition):
    return t #Transition(re.split("_loop", t.src)[0], t.condition, t.action, t.output,  re.split("_loop", t.tgt)[0]) \
              #  if "loop" in ((t.src) + (t.tgt)) else t

def concretize_transitions(program, looping_program, indices_and_state_list, state_pred_label_to_formula, incompatible_state):
    transitions = looping_program.env_transitions + looping_program.con_transitions
    smt_checker = SMTChecker()

    # ignore the mismatch state
    new_indices_and_state_list = indices_and_state_list
    concretized = []
    for (i, st) in new_indices_and_state_list:
        if int(i) != -1:
            concretized += [(looping_to_normal(transitions[int(i)]), st)]
        else:
            stutter_trans = stutter_transition(program, [q for q in program.states if st[str(q)] == "TRUE"][0],
                                               st["turn"] == "env")
            if stutter_trans == None:
                raise Exception("stuttering transition not found")
            else:
                concretized += [(stutter_trans, st)]

    # two options, either we stopped because of a predicate mismatch, or a transition mismatch
    incompatibility_formula = []
    if incompatible_state["compatible_states"] == "FALSE" or incompatible_state["compatible_outputs"] == "FALSE":
        if program.deterministic:
            return concretized[:-1], ([neg(concretized[-1][0].condition)], concretized[-1][1]), concretized[-1]
        else:
            # if program is not deterministic, we need to identify the transitions the counterstrategy wanted to take rather than the one the program actually took
            try:
                state_before_mismatch = concretized[-2][1]
            except Exception as e:
                raise e
            src_state = concretized[-2][0].tgt
            tgt_state_env_wanted = [p for p in program.states if incompatible_state["mon_" + str(p)] == "TRUE"][0]
            outputs_env_wanted = [p for p in program.out_events if incompatible_state["mon_" + str(p)] == "TRUE"]
            outputs_env_wanted += [neg(p) for p in program.out_events if incompatible_state["mon_" + str(p)] == "FALSE"]
            if incompatible_state["turn"] == "mon_env":
                candidate_transitions = [t for t in program.env_transitions if
                                         t.src == src_state and t.tgt == tgt_state_env_wanted and set(t.output) == set(
                                             outputs_env_wanted)]
                if tgt_state_env_wanted == src_state:
                    stutter = stutter_transition(program, src_state, True)
                    if stutter is not None:
                        candidate_transitions.append(stutter)
            elif incompatible_state["turn"] == "mon_con":
                candidate_transitions = [t for t in program.con_transitions if
                                         t.src == src_state and t.tgt == tgt_state_env_wanted and set(t.output) == set(
                                             outputs_env_wanted)]
                if tgt_state_env_wanted == src_state:
                    stutter = stutter_transition(program, src_state, False)
                    if stutter is not None:
                        candidate_transitions.append(stutter)
            else:
                raise Exception("Mismatches should only occur at mon_env or mon_con turns")

            compatible_with_abstract_state = [state_pred_label_to_formula[p] for p in state_pred_label_to_formula.keys()
                                              if isinstance(p, Variable) and state_before_mismatch[str(p)] == "TRUE"]
            compatible_with_abstract_state += [neg(state_pred_label_to_formula[p]) for p in
                                               state_pred_label_to_formula.keys() if
                                               isinstance(p, Variable) and state_before_mismatch[str(p)] == "FALSE"]

            abstract_state = conjunct_formula_set(compatible_with_abstract_state)
            env_desired_transitions = [t for t in candidate_transitions
                                       if smt_checker.check(And(*abstract_state.to_smt(program.symbol_table),
                                                                *t.condition.to_smt(program.symbol_table)))]
            formula = disjunct_formula_set([t.condition for t in env_desired_transitions] + [
                propagate_negations(neg(concretized[-1][0].condition))])
            return concretized[:-1], ([formula], concretized[-1][1]), concretized[-1]
    else:
        env_pred_state = None
        if incompatible_state["compatible_state_predicates"] == "FALSE" or incompatible_state[
            "compatible_tran_predicates"] == "FALSE":
            # pred mismatch
            incompatibility_formula += preds_in_state(incompatible_state, state_pred_label_to_formula)
            #TODO we wanted to take the wrong transition, but the condition at state concretized[-1][1], not at incompatible_state
            # incompatibility_formula += [neg(concretized[-1][0].condition)]
            env_pred_state = (incompatibility_formula, incompatible_state)

        return concretized, env_pred_state, concretized[-1]


def preds_in_state(ce_state: dict, state_pred_label_to_formula):
    return [state_pred_label_to_formula[Variable(p)] for p, v in ce_state.items() if p.startswith("pred_") and v == "TRUE"] \
                + [state_pred_label_to_formula[neg(Variable(p))] for p, v in ce_state.items() if
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
        preds = {p for p in formula.sub_formulas_up_to_associativity() if not any(v for v in p.variablesin() if symbol_table[str(v)].type != "bool")}
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
    env_state_dict = {s: [t.condition for t in program.env_transitions if t.src == s] for s in program.states}

    symbol_table = program.symbol_table
    smt_checker = SMTChecker()

    for (s, conds) in env_state_dict.items():
        # Assuming satisfiability already checked
        sat_conds = [cond for cond in conds]
        # sat_conds = [cond for cond in conds if smt_checker.check(And(*cond.to_smt(symbol_table)))]
        # for cond in conds:
        #     if cond not in sat_conds:
        #         print("WARNING: " + str(cond) + " is not satisfiable, see transitions from state " + str(s))

        for i, cond in enumerate(sat_conds):
            for cond2 in sat_conds[i + 1:]:
                if smt_checker.check(And(*(cond.to_smt(symbol_table) + cond2.to_smt(symbol_table)))):
                    print("WARNING: " + str(cond) + " and " + str(
                        cond2) + " are satisfiable together, see environment transitions from state " + str(s))
                    return False

    con_state_dict = {s: [t.condition for t in program.con_transitions if t.src == s] for s in program.states}

    for (s, conds) in con_state_dict.items():
        # Assuming satisfiability already checked
        sat_conds = [cond for cond in conds]
        # sat_conds = [cond for cond in conds if smt_checker.check(And(*cond.to_smt(symbol_table)))]
        # for cond in conds:
        #     if cond not in sat_conds:
        #         print("WARNING: " + str(cond) + " is not satisfiable, see transitions from state " + str(s))
        for i, cond in enumerate(sat_conds):
            for cond2 in sat_conds[i + 1:]:
                if smt_checker.check(And(*(cond.to_smt(symbol_table) + cond2.to_smt(symbol_table)))):
                    print("WARNING: " + str(cond) + " and " + str(
                        cond2) + " are satisfiable together, see controller transitions from state " + str(s))
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


def safe_update_dict_value(d : dict, k, v_dict):
    if k in d.keys():
        d[k].update(v_dict)
    else:
        d[k] = v_dict


def function_is_of_natural_type(f: Formula, invars: Formula, symbol_table):
    # TODO, should we conjunct or disjunct invars?
    smt_checker = SMTChecker()

    return not smt_checker.check(And(*conjunct(conjunct_formula_set(invars), BiOp(f, "<", Value(0))).to_smt(symbol_table)))


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



def guarded_action_transitions_to_normal_transitions(guarded_transition, valuation, env_events, con_events, outputs, symbol_table):
    if str(guarded_transition.condition) == "otherwise":
        # check that no guarded actions
        for (act, guard) in guarded_transition.action:
            if guard is not None or str(guard) != "true":
                raise Exception("Otherwise transitions cannot have guarded actions")
        return [guarded_transition]

    unguarded_acts = []
    guarded_acts = {act: set() for (act, _) in guarded_transition.action}
    for (act, guard) in guarded_transition.action:
        new_guard = conjunct(guard, type_constraints(act.left, symbol_table))
        guarded_acts[act].add(new_guard)

    guarded_acts = {act: g_set for act, g_set in guarded_acts.items() if len(g_set) > 0}

    if len(guarded_acts) == 0:
        return [Transition(guarded_transition.src, guarded_transition.condition, unguarded_acts, guarded_transition.output, guarded_transition.tgt)]

    transitions = []

    checker = SMTChecker()
    symbol_table = {}
    for t_val in valuation:
        symbol_table[t_val.name] = t_val
        symbol_table[t_val.name + "_next"] = TypedValuation(t_val.name + "_next", t_val.type, t_val.value)

    for ev in outputs + env_events + con_events:
        symbol_table[ev.name] = TypedValuation(str(ev), "bool", None)

    act_guard_sets = set()
    act_guard_sets.add(frozenset({}))
    for act in guarded_acts.keys():
        new_act_guard_sets = set()
        # check that each guard is mutually exclusive with the other guards
        for guard1 in guarded_acts[act]:
            for guard2 in guarded_acts[act]:
                if guard1 != guard2 and sat(conjunct(guard1, guard2), symbol_table, checker):
                    raise Exception("Guarded actions are not mutually exclusive: " + str(guard1) + " and " + str(
                        guard2) + " in " + str(guarded_transition))
            for act_guard_set in act_guard_sets:
                guard1true = frozenset(act_guard_set | {(act, guard1)})
                guard1false = frozenset(act_guard_set | {(None, neg(guard1))})
                if sat(conjunct_formula_set([g for (_,g) in guard1true]), symbol_table, checker):
                    new_act_guard_sets.add(guard1true)
                if sat(conjunct_formula_set([g for (_,g) in guard1false]), symbol_table, checker):
                    new_act_guard_sets.add(guard1false)
        act_guard_sets = new_act_guard_sets

    for act_guard_set in act_guard_sets:
        action_guards = conjunct_formula_set(sorted(list({guard for (_, guard) in act_guard_set}), key=lambda x : str(x)))
        new_guard = conjunct(guarded_transition.condition, action_guards)
        if not sat(new_guard, symbol_table, checker):
            continue

        actions = [act for (act, _) in act_guard_set if act != None]

        transitions.append(Transition(guarded_transition.src, propagate_negations(new_guard),
                           unguarded_acts + actions, guarded_transition.output, guarded_transition.tgt))

    # debug
    collect_guards = []
    for t in transitions:
        collect_guards += [t.condition]
    if sat((conjunct(guarded_transition.condition, neg(disjunct_formula_set(collect_guards)))), symbol_table, checker):
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

def stringify_formula(f):
    if isinstance(f, BiOp):
        return BiOp(stringify_formula(f.left), f.op, stringify_formula(f.right))
    elif isinstance(f, UniOp):
        return UniOp(f.op, stringify_formula(f.right))
    elif isinstance(f, MathExpr) or isinstance(f, Variable):
        return stringify_pred(f)
    else:
        return f

def powerset_complete(SS: set):
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

powersets = {}
def powerset(S: set):
    if frozenset(S) in powersets.keys():
        return powersets[frozenset(S)]
    else:
        subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
        subsets = sorted(list(map(set, subsets)), key=lambda x: len(x))

        powersets[frozenset(S)] = subsets
        return subsets
