import logging

from pysmt.fnode import FNode
from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop
from programs.abstraction.interface.predicate_abstraction import PredicateAbstraction
from programs.analysis.smt_checker import SMTChecker, binary_interpolant
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import ce_state_to_formula, ground_formula_on_ce_state_with_index, project_ce_state_onto_ev, \
    fnode_to_formula, reduce_up_to_iff
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import true, neg, conjunct_formula_set, conjunct, dnf_safe
from prop_lang.value import Value
from prop_lang.variable import Variable


def safety_refinement(program: Program,
                      predicate_abstraction: PredicateAbstraction,
                      agreed_on_transitions,
                      disagreed_on_state,
                      ce,
                      allow_user_input: bool,
                      keep_only_bool_interpolants: bool,
                      conservative_with_state_predicates: bool):
    symbol_table = predicate_abstraction.get_symbol_table()
    if allow_user_input:
        new_state_preds = interactive_state_predicates()
    else:
        pred_formula = conjunct_formula_set([p for p in disagreed_on_state[0]])
        new_state_preds = counterexample_interpolation(ce,
                                                       agreed_on_transitions,
                                                       ([pred_formula], disagreed_on_state[1]),
                                                       symbol_table, program, use_dnf=True)

        if len(new_state_preds) == 0:
            logging.info("No state predicates identified.")
            if allow_user_input:
                new_state_preds = interactive_state_predicates()
            else:
                logging.info("I will try using the values of variables instead..")
                vars_mentioned_in_preds = {v for p in disagreed_on_state[0] for v in p.variablesin() if
                                           not str(v).endswith("_prev")}
                new_state_preds |= {BiOp(v, "=", Value(state[str(v)])) for v in vars_mentioned_in_preds for state
                                    in [st for (_, st) in agreed_on_transitions + [disagreed_on_state]]}
        else:
            logging.info("Found state predicates: " + ", ".join([str(p) for p in new_state_preds]))

    state_predicates = predicate_abstraction.get_state_predicates()
    new_all_preds = [x.simplify() for x in new_state_preds] + state_predicates

    new_all_preds = reduce_up_to_iff(predicate_abstraction.get_state_predicates(),
                                     list(new_all_preds),
                                     symbol_table
                                     | {str(v): TypedValuation(str(v),
                                                               symbol_table[str(v).removesuffix("_prev")].type,
                                                               "true")
                                        for p in new_all_preds
                                        for v in p.variablesin()
                                        if str(v).endswith(
                                             "prev")})  # TODO symbol_table needs to be updated with prevs

    if len(new_all_preds) < len(set(state_predicates)):
        raise Exception("There are somehow less state predicates than previously.")

    if len(new_all_preds) == len(set(state_predicates)):
        # check_for_nondeterminism_last_step(program_actually_took[1], predicate_abstraction.py.program, True)
        logging.info(
            "New state predicates (" + ", ".join([str(p) for p in new_state_preds]) + ") are a subset of "
                                                                                      "previous predicates."
        )
        logging.info("I will try using the values of variables instead..")
        vars_mentioned_in_preds = {v for p in new_state_preds for v in p.variablesin()}
        new_state_preds = {BiOp(v, "=", Value(state[str(v)]))
                           for v in vars_mentioned_in_preds
                           for state in [st for (_, st) in agreed_on_transitions + [disagreed_on_state]]}
        new_all_preds = {x.simplify() for x in
                         new_state_preds | {p for p in state_predicates if p not in state_predicates}}
        new_all_preds = reduce_up_to_iff(set(state_predicates),
                                         list(new_all_preds),
                                         symbol_table
                                         | {str(v): TypedValuation(str(v),
                                                                   symbol_table[
                                                                       str(v).removesuffix("_prev")].type,
                                                                   "true")
                                            for p in new_all_preds
                                            for v in p.variablesin()
                                            if str(v).endswith(
                                                 "prev")})
        if len(new_all_preds) <= len(set(state_predicates)):
            return False, None

    if keep_only_bool_interpolants:
        bool_interpolants = [p for p in new_state_preds if
                             p not in state_predicates and p in new_all_preds and 0 == len(
                                 [v for v in p.variablesin() if
                                  symbol_table[str(v)].type != "bool" and symbol_table[
                                      str(v)].type != "boolean"])]
        if len(bool_interpolants) > 0:
            new_all_preds = [p for p in new_all_preds if p in bool_interpolants or p in state_predicates]
    if conservative_with_state_predicates:
        # TODO some heuristics to choose state preds
        new_state_preds = [p for p in new_all_preds if p not in state_predicates]
        if len(new_state_preds) == 0:
            raise Exception("No new state predicates identified.")
        # get the number of variables associated with each predicates
        ordered_according_to_no_of_vars_used = [[p for p in new_state_preds if len(p.variablesin()) == n] for n in
                                                range(1, len(program.valuation) + 1)]
        ordered_according_to_no_of_vars_used = [ps for ps in ordered_according_to_no_of_vars_used if
                                                len(ps) > 0]
        new_all_preds = state_predicates + (ordered_according_to_no_of_vars_used[0] if len(
            ordered_according_to_no_of_vars_used) > 0 else [])

    logging.info("Using: " + ", ".join([str(p) for p in new_all_preds if p not in state_predicates]))

    return True, [p for p in new_all_preds if p not in state_predicates]


def counterexample_interpolation(ce: [dict],
                                 agreed_on_transitions: [(Transition, dict)],
                                 disagreed_on_state: (Formula, dict),
                                 symbol_table,
                                 program,
                                 use_dnf=False) -> [FNode]:
    # we collect interpolants in this set
    Cs = set()
    # TODO
    #  sometimes we should get the condition of a transition as predicate
    #  consider a condition checking that a variable is even
    #  we may get as interpolants the values of the variable

    concurring_transitions = agreed_on_transitions

    # TODO, should the below be needed? The first transition should always be correct
    # this is a hack to ensure correct behaviour when there is a mismatch with only one transition (disagreed_on)
    # since interpolation requires len(concurring_transitions) to be at least one 1
    if concurring_transitions == []:
        concurring_transitions = [(Transition(program.initial_state, true(), [], [], program.initial_state), ce[0])]

    # TODO why aren't se just conjuncting disagreed_on_state[0]?
    for s in disagreed_on_state[0]:
        for j in reversed(range(0, len(concurring_transitions) + 1)):
            Css = path_interpolation(program,
                                     concurring_transitions,
                                     (neg(s), disagreed_on_state[1]),
                                     j,
                                     symbol_table,
                                     use_dnf=use_dnf)
            if Css is None:
                logging.info("I think that interpolation is being checked against formulas that are not contradictory.")
                break
            # if B is itself inconsistent
            if len(Cs) == 1 and isinstance(list(Cs)[0], Value):
                if list(Cs)[0].is_true():
                    break
                elif list(Cs)[0].is_false():
                    break

            for C in Css:
                if isinstance(C, BiOp) and C.op[0] == "&":
                    Cs |= set(C.sub_formulas_up_to_associativity())
                elif isinstance(C, Value):
                    if C.is_true():
                        continue
                    elif C.is_false():
                        continue
                else:
                    Cs |= {C}

    return Cs


def path_interpolation(program: Program, concurring_transitions: [(Transition, dict)],
                       disagreed_on_state: (Formula, dict), cut_point: int, symbol_table, use_dnf=False):
    assert cut_point <= len(concurring_transitions)
    assert len(concurring_transitions) > 0

    logic = "QF_UFLRA"  # TODO what to put here?
    smt_checker = SMTChecker()

    # this will be used to add intermediate variables for each monitor state
    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys()]

    # symbol table is updated with intermediate variables (plus last one, len(prefix), for state after last transition
    new_symbol_table = {}
    for i in range(0, len(concurring_transitions) + 1):
        new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

    # this will be used to generalise the interpolants references to intermediate variables to the original variable name
    # reset_vars_i = lambda i, suffix : [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v + "_" + suffix)) for v in symbol_table.keys()]
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in
                  range(0, len(concurring_transitions) + 1)]

    init_prop = ce_state_to_formula(concurring_transitions[0][1], symbol_table).replace(ith_vars(0))

    path_formula_set_A = []
    path_formula_set_A += [init_prop]
    for i in range(0, cut_point):
        path_formula_set_A += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]

    path_formula_A = conjunct_formula_set(path_formula_set_A)

    path_formula_set_B = []
    upper_bound = len(concurring_transitions)
    i = cut_point
    while i < upper_bound:
        path_formula_set_B += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]
        i += 1

    disagreed_on_value_state = disagreed_on_state[1]
    projected_condition = disagreed_on_state[0].replace(ith_vars(len(concurring_transitions)))
    if any(v for v in projected_condition.variablesin() if "_prev" in str(v)):
        projected_condition = projected_condition.replace(
            [BiOp(Variable(str(v)), ":=", Variable(str(v).split("_prev")[0] + "_" + str(i - 1))) for v in
             projected_condition.variablesin() if "_prev" in str(v)])
    grounded_condition = ground_formula_on_ce_state_with_index(projected_condition,
                                                               project_ce_state_onto_ev(disagreed_on_value_state,
                                                                                        program.env_events
                                                                                        + program.con_events),
                                                               len(concurring_transitions))

    # some simplification before DNFing
    if isinstance(grounded_condition, BiOp) and grounded_condition.op[0] == "&":
        Bs = list(map(neg, grounded_condition.sub_formulas_up_to_associativity()))
    elif isinstance(grounded_condition, UniOp) and grounded_condition.op == "!":
        if isinstance(grounded_condition.right, BiOp) and grounded_condition.right.op[0] == "|":
            Bs = grounded_condition.right.sub_formulas_up_to_associativity()
        else:
            Bs = [grounded_condition.right]
    else:
        Bs = [neg(grounded_condition)]

    if use_dnf:
        new_Bs = []
        for b in Bs:
            after_dnf = dnf_safe(b, new_symbol_table)
            if isinstance(after_dnf, BiOp) and after_dnf.op[0] == "|":
                new_Bs += after_dnf.sub_formulas_up_to_associativity()
            else:
                new_Bs += [after_dnf]
        Bs = new_Bs

    Cs = set()

    for BB in Bs:
        path_formula_B = conjunct_formula_set(path_formula_set_B + [BB])

        A = And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))
        B = And(*path_formula_B.to_smt(new_symbol_table))

        C = binary_interpolant(A, B)

        if C is not None:
            Cf = fnode_to_formula(C)
            previous_vars_related_to_current_vars = [v for v in Cf.variablesin() if Variable(
                str(v).rsplit("_", 1)[0] + "_" + str(int(str(v).rsplit("_", 1)[1]) - 1)) in Cf.variablesin()]
            if len(previous_vars_related_to_current_vars) > 0:
                # ground previous variables on their values; TODO instead of just looking one step back, have to go back to the first action, or just use the variables value in the previous step
                for v in previous_vars_related_to_current_vars:
                    var_name = (str(v).split("_")[0])
                    prev_var = Variable(var_name + "_" + str(i - 1))
                    Cf = Cf.replace(
                        [BiOp(prev_var, ":=", act.right) for act in concurring_transitions[i - 1][0].action if
                         str(act.left) == var_name])
            Cf = Cf.replace(reset_vars)
            Cs |= {Cf}

    if len(Cs) == 0:
        return None
    else:
        return Cs


def interactive_state_predicates():
    finished = False
    new_preds = []
    while not finished:
        try:
            text = input("Any suggestions of state predicates?")
            if len(text.strip(" ")) == 0:
                finished = True
            else:
                new_preds = set(map(string_to_prop, text.split(",")))
                finished = True
        except Exception as e:
            pass
    return new_preds
