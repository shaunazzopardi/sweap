import logging
import multiprocessing as mp
import time
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.util.InvertibleMap import InvertibleMap
from analysis.abstraction.effects_abstraction.util.effects_to_automaton import effects_to_explicit_automaton_abstraction
from analysis.abstraction.effects_abstraction.util.effects_util import merge_transitions, relevant_pred
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionTransitionType, LTLAbstractionBaseType, \
    LTLAbstractionStructureType, LTLAbstractionType, LTLAbstractionOutputType
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis import parse_hoa
from synthesis.mealy_machine import MealyMachine
from programs.typed_valuation import TypedValuation

logger = logging.getLogger(__name__)

from joblib import Parallel, delayed

from programs.program import Program
from programs.transition import Transition
from programs.util import add_prev_suffix, transition_formula, powerset_complete
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    true, false, sat, simplify_formula_with_math, is_contradictory, label_pred, stringify_pred, should_be_math_expr, \
    is_conjunction_of_atoms


class EffectsAbstraction(PredicateAbstraction):
    def __init__(self, program: Program):
        self.formula_to_trans = {}
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_relevant_preds = {}
        self.abstract_effect_irrelevant_preds = {}
        self.abstract_effect_tran_preds_constant = {}
        self.combined_automata_abstraction = None

        self.init_program_trans = None
        self.abstract_guard = None
        self.abstract_guard_disjuncts = None
        self.state_predicates = []
        self.transition_predicates = []

        self.interpolants = set()
        self.ltl_constraints = []
        self.loops = []
        self.var_relabellings = {}

        self.abs_trans_to_program_transitions = None

        self.program_transitions_to_abstract = None

        self.state_to_abs_transitions = None
        self.all_program_trans = None

        self.abstraction = None
        self.program = program
        self.cache = {}
        self.f_cache = {}
        self.loop_counter = 0
        self.loops = []

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions(parallelise=True)

        # Formula -> (P -> [P])
        for t in self.all_program_trans:
            formula = transition_formula(t)
            # TODO these should eventually all depend on formula not transition,
            #  note that multiple transitions may have the same formula
            self.formula_to_trans[formula] = t
            self.abstract_effect_invars[t] = []
            self.abstract_effect_constant[t] = []
            self.abstract_effect_tran_preds_constant[t] = []

        self.symbol_table = {v:tv for v, tv in program.symbol_table.items()}

    def abstract_program_transition(self, trans: Transition, symbol_table):
        disjuncts, formula = self.abstract_guard_explicitly(trans.condition, self.program.env_events + self.program.con_events, symbol_table)
        return trans, disjuncts, formula


    def abstract_program_transitions(self, parallelise=True):
        # TODO here get stutter transitions
        #    can treat them specially by considering the work already done for transitions from their state
        orig_transitions, stutter = self.program.complete_transitions_stutter_explicit()

        self.abstract_guard = {}
        self.abstract_guard_disjuncts = {}

        self.init_program_trans = []

        all_trans = orig_transitions + stutter
        init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        self.init_program_trans = [t.add_condition(init_conf) for t in all_trans if
                                   t.src == self.program.initial_state and sat(conjunct(init_conf, t.condition),
                                                                               self.program.symbol_table)]

        if parallelise:
            arg1 = []
            arg2 = []
            arg3 = []
            for t in all_trans + self.init_program_trans:
                arg1.append(t)
                arg2.append(self.program.env_events + self.program.con_events)
                arg3.append(self.program.symbol_table)
            with Pool(mp.cpu_count()) as pool:
                results = pool.map(abstract_guard_explicitly_parallel, zip(arg1, arg2, arg3))
        else:
            results = [self.abstract_program_transition(t, self.program.symbol_table) for t in all_trans + self.init_program_trans]

        for t, disjuncts, formula in results:
            self.abstract_guard[t] = formula
            self.abstract_guard_disjuncts[t] = disjuncts
            empty_effects = InvertibleMap()
            true_set = {frozenset()}
            empty_effects.put(frozenset(), frozenset(true_set))
            self.abstract_effect[t] = {E: empty_effects for _, E in disjuncts}
            self.abstract_effect_relevant_preds[t] = {E: set() for _, E in disjuncts}
            self.abstract_effect_irrelevant_preds[t] = {E: set() for _, E in disjuncts}

        self.all_program_trans = orig_transitions + self.init_program_trans + stutter

    def abstract_guard_explicitly(self, guard, events, symbol_table):
        vars_in_cond = guard.variablesin()
        if is_conjunction_of_atoms(guard):
            conjuncts = guard.sub_formulas_up_to_associativity()
            cond = []
            env_con_events = set()
            for c in conjuncts:
                if not any(v for v in c.variablesin() if v not in events):
                    env_con_events.add(c)
                else:
                    cond.append(c)
            E = frozenset(env_con_events)
            int_disjuncts_only_events = [E]
            return [(conjunct_formula_set(cond), E)], int_disjuncts_only_events

        events_in_cond = [e for e in vars_in_cond if e in events]
        powerset = powerset_complete(events_in_cond)
        int_disjuncts_only_events = [E for E in powerset if
                                     sat(conjunct_formula_set(E | {guard}), self.program.symbol_table)]

        satisfying_behaviour = int_disjuncts_only_events
        dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
        disjuncts = []
        for E in satisfying_behaviour:
            if not E:
                logger.info("empty E " + str(guard))
            guard_E = guard.replace_vars(lambda x: true() if x in E else false() if neg(x) in E else x)
            try:
                guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
            except Exception as e:
                # TODO what is this exception caused by??
                guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
                logging.info(str(e))
            disjuncts.append((guard_E_simplified, E))
        return disjuncts, dnfed

    def abstract_guard(self, guard: Formula, events, symbol_table, use_set_method=True):
        return self.abstract_guard_explicitly(guard, events, symbol_table)

    def compute_abstract_effect_with_p(self, t: Transition, Es, old_effects, predicate):
        if len(old_effects) == 0:
            return t, transition_formula(t), [], [], Es, old_effects
        # TODO
        #   1. keep track of powersets of preds that are satisfiable with guard
        #   then consider the effects of the actions on the new predicates
        #   2. in the first step we do some optimisation, by not considering predicates with variables unmentioned in
        #   guard and right-hand side of actions
        #   3. in the second step we do some optimisation, by checking whether the variables in the candidate effect
        #   predicate are modified in the actions or not
        #   4. if a predicate truth in the next step cannot be determined, then do not explode effect set, but keep track
        #   in separate set, and try to determine it s truth when new predicates are added

        is_tran_pred = lambda q: any(True for v in q.variablesin() if str(v).endswith("_prev"))

        action = t.action
        # TODO, if no vars modified, then only need need to abstract guards in terms of predicates, then they maintain same value

        vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
        vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in
                                                a.right.variablesin()]

        t_formula = transition_formula(t)

        invars = []
        constants = []
        new_effects = {x: y for x, y in old_effects.items()}

        variable_used_in_guard = any(True for v in predicate.variablesin() if v in t.condition.variablesin())
        value_modified = any(True for v in predicate.variablesin()
                                    if v in vars_modified_in_action_without_identity +
                                            vars_used_in_action_without_identity)
        # if the predicate is a state predicate and is not mentioned in both the guard and action
        if not is_tran_pred(predicate) and not variable_used_in_guard and not value_modified:
            invars = [predicate]
            return t, t_formula, invars, constants, Es, new_effects
        # if the predicate is an inc or dec transition predicate and is not mentioned in the action
        elif (is_tran_pred(predicate)
              and isinstance(predicate, BiOp) and predicate.op in ["<", ">"]  # This is only applicable for decs and incs
              and not value_modified):
            constants = [neg(predicate)]
        # if the predicate is always false after the transition
        elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table):
            constants = [neg(predicate)]
        # if the predicate is always true after the transition
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table):
            constants = [(predicate)]
        # if the predicate is maintained by the transition
        elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]),
                              self.program.symbol_table) and \
                is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]),
                                 self.program.symbol_table):
            # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
            invars = [(predicate)]

        action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
        if len(constants) > 0 or len(invars) > 0:
            # TODO optimisation: if no variable in predicate is mentioned in guard,
            #  then just explode the precondition set without any sat checks
            #  Correction: eh, need to consider when predicate is relevant for guard:
            #    if they have variables in common?
            #    if the predicate has variables in common with other relevant predicates?
            #    if not relevant, need to keep track, and consider adding it later
            #    or is there a way to avoid adding later? the only reason to add later would be that a new relevant pred
            #    has vars in common with an irrelevant pred; could we instead try to identify invariant relationships
            #    between the predicates?
            # TODO, don t want to explode before needed, collect all such predicates,
            #  then add iff a new predicate to be added may be affected by the collected predicates
            for (guard_disjunct, E) in Es:
                formula_pos = add_prev_suffix(conjunct(guard_disjunct, predicate))
                formula_pos = conjunct(formula_pos, action_formula)
                if sat(formula_pos, self.program.symbol_table):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = add_prev_suffix(conjunct(guard_disjunct, neg(predicate)))
                formula_neg = conjunct(formula_neg, action_formula)
                if sat(formula_neg, self.program.symbol_table):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()

                # old_effects[E] is an InvertibleMap
                for (nextPs, Pss) in old_effects[E].items():
                    if not relevant_pred(t, nextPs, predicate):
                        # new_effects[E] = old_effects[E]
                        newNextPss.put(nextPs, Pss)
                        continue

                    new_pos_Ps = set()
                    new_neg_Ps = set()
                    for Ps in Pss:
                        # if p was true before, is p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs),
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_pos_Ps.add(Ps | {predicate})

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_neg_Ps.add(Ps | {neg(predicate)})
                    # self.all_pred_states.add(frozenset(new_pos_Ps))
                    # self.all_pred_states.add(frozenset(new_neg_Ps))

                    new_now = frozenset(P for P in new_neg_Ps | new_pos_Ps)
                    if len(new_now) > 0:
                        newNextPss.put(nextPs, new_now)

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    if E in new_effects.keys():
                        new_effects.pop(E)

                    Es.remove((guard_disjunct, E))
        else:
            prev_predicate = add_prev_suffix(predicate)
            for (guard_disjunct, E) in Es:
                # E_formula = add_prev_suffix(conjunct_formula_set(E))
                new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))
                formula_pos = conjunct(new_formula, prev_predicate)
                if sat(formula_pos, self.program.symbol_table):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = conjunct(new_formula, neg(prev_predicate))
                if sat(formula_neg, self.program.symbol_table):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()

                # old_effects[E] is an InvertibleMap
                for (nextPs, Pss) in old_effects[E].items():
                    nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                    nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                    new_pos_Ps = set()
                    new_neg_Ps = set()
                    for Ps in Pss:
                        # if p was true before, is p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_pos_Ps.add(Ps | {predicate})

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_pos_Ps.add(Ps | {neg(predicate)})

                        # if p was true before, is not p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_neg_Ps.add(Ps | {predicate})

                        # if p was false before, is not p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_neg_Ps.add(Ps | {neg(predicate)})

                    if len(new_pos_Ps) > 0:
                        newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                    if len(new_neg_Ps) > 0:
                        newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    if E in new_effects.keys():
                        new_effects.pop(E)

                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def add_transition_predicate_to_t(self, t: Transition, Es, old_effects, predicate):
        if len(old_effects) == 0:
            return t, transition_formula(t), [], [], Es, old_effects

        if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
            raise Exception(str(predicate) + " is not a transition predicate.")

        action = t.action

        t_formula = transition_formula(t)

        invars = []
        constants = []
        new_effects = {x: y for x, y in old_effects.items()}
        # if the transition predicate is not mentioned in the action
        if is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table):
            constants = [(predicate)]
        # if cannot determine exactly whether to the pred is a constant, then for replicate each post state
        # for each possibility
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            for (guard_disjunct, E) in Es:
                # E_formula = add_prev_suffix(conjunct_formula_set(E))
                new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))

                newNextPss = InvertibleMap()

                # old_effects[E] is an InvertibleMap
                for (nextPs, Pss) in old_effects[E].items():
                    nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                    nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                    new_pos_Ps = set()
                    new_neg_Ps = set()
                    for Ps in Pss:
                        if sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                        conjunct(new_formula,
                                                 conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                               self.program.symbol_table):
                            new_pos_Ps.add(Ps)

                        if sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                        conjunct(new_formula,
                                                 conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                               self.program.symbol_table):
                            new_neg_Ps.add(Ps)

                    if len(new_pos_Ps) > 0:
                        newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                    if len(new_neg_Ps) > 0:
                        newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    if E in new_effects.keys():
                        new_effects.pop(E)

                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def pretty_print_abstract_effect(self):
        for t in self.abstract_effect.keys():
            logging.info(str(t))
            for E in self.abstract_effect[t].keys():
                if len(E) == 0:
                    logging.info("\tevents: " + "true")
                else:
                    logging.info("\tevents: " + ", ".join(str(e) for e in E))
                for nextPs in self.abstract_effect[t][E].keys():
                    logging.info("\t\tnext: " + ("true" if len(nextPs) == 0 else " and ".join(str(p) for p in nextPs)))
                    logging.info("\t\tnow: " + (" or \n\t\t\t".join(
                        "true" if len(nowPs) == 0 else "(" + " and ".join(str(p) for p in nowPs) + ")" for nowPs in
                        self.abstract_effect[t][E][nextPs])))

    def add_predicates(self,
                       new_state_predicates: [Formula],
                       new_transition_predicates: [Formula],
                       parallelise=True):
        for p in new_state_predicates:
            self.var_relabellings[p] = stringify_pred(p)
        for p in new_transition_predicates:
            self.var_relabellings[p] = stringify_pred(p)

        self.interpolants.update(new_state_predicates)
        self.add_state_predicates(new_state_predicates, parallelise)

        self.add_transition_predicates(new_transition_predicates, parallelise)

        self.pretty_print_abstract_effect()

    def add_constraints(self, new_ltl_constraints: [Formula]):
        processed_ltl_constraints = []
        for constraint in new_ltl_constraints:
            processed = constraint.replace_formulas(self.var_relabellings)
            processed_ltl_constraints.append(processed)
        self.ltl_constraints.extend(processed_ltl_constraints)

    def add_state_predicates(self, new_state_predicates: [Formula], parallelise=True):
        if len(new_state_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()
        # self.all_pred_states = set()
        for p in new_state_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_state_predicates)):
                    TypedValuation(str(label_pred(p, new_state_predicates)), "bool", true())})

            if parallelise:# and len(self.state_predicates) > 4:
                arg1 = []
                arg2 = []
                arg3 = []
                arg4 = []
                arg5 = []
                for t in self.abstract_guard.keys():
                    arg1.append(t)
                    arg2.append(self.abstract_guard_disjuncts[t])
                    arg3.append(self.abstract_effect[t])
                    arg4.append(p)
                    arg5.append(self.program.symbol_table)
                with Pool(mp.cpu_count()) as pool:
                    results = pool.map(compute_abstract_effect_with_p_parallel, zip(arg1, arg2, arg3, arg4, arg5))
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p
                # results = config.parallel(
                #     delayed(self.compute_abstract_effect_with_p)(t, self.abstract_guard_disjuncts[t],
                #                                                  self.abstract_effect[t], p)
                #     for t in self.abstract_guard.keys())# if t not in self.init_program_trans)
            else:
                results = []
                for t in self.abstract_guard.keys():
                    results.append(self.compute_abstract_effect_with_p(t, self.abstract_guard_disjuncts[t],
                                                                           self.abstract_effect[t], p))

            # TODO can optimise, since same t may be both env or con
            for t, t_formula, invars, constants, Es, new_effects in results:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_constant[t] += constants
                self.abstract_guard_disjuncts[t] = Es
                self.abstract_effect[t] = new_effects

        if config.debug:
            # sanity check
            for t, E_effects in self.abstract_effect.items():
                t_f = transition_formula(t)
                for E, next_nows in E_effects.items():
                    f = conjunct(t_f, add_prev_suffix(conjunct_formula_set(E)))
                    for next, nows in next_nows.items():
                        for now in nows:
                            effects_f = disjunct_formula_set([conjunct(conjunct_formula_set(next),
                                                               add_prev_suffix(conjunct_formula_set(now)))])
                            to_check = conjunct(f, effects_f)
                            if not sat(to_check, self.symbol_table):
                                raise Exception("something wrong in effectsabsttraction")

        end = time.time()
        logger.info(end - start)

        start = time.time()
        # self.prune_predicate_sets()
        # self.prune_based_on_explicit_abstraction()
        end = time.time()
        logger.info(end - start)

        self.state_predicates += new_state_predicates

    def add_transition_predicates(self, new_transition_predicates: [Formula],
                                  parallelise=True):
        if len(new_transition_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()
        # self.all_pred_states = set()
        for p in new_transition_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_transition_predicates)):
                    TypedValuation(str(label_pred(p, new_transition_predicates)), "bool", true())})

            if parallelise:
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p
                arg1 = []
                arg2 = []
                arg3 = []
                arg4 = []
                arg5 = []
                for t in self.abstract_guard.keys():
                    arg1.append(t)
                    arg2.append(self.abstract_guard_disjuncts[t])
                    arg3.append(self.abstract_effect[t])
                    arg4.append(p)
                    arg5.append(self.program.symbol_table)

                with Pool(mp.cpu_count()) as pool:
                    results = pool.map(add_transition_predicate_to_t_parallel, zip(arg1, arg2, arg3, arg4, arg5))
                # results = config.parallel(
                #     delayed(self.add_transition_predicate_to_t)(t, self.abstract_guard_disjuncts[t],
                #                                                 self.abstract_effect[t], p) for t in
                #     self.abstract_guard.keys())
            else:
                results = []
                for t in self.abstract_guard.keys():
                    results.append(self.add_transition_predicate_to_t(t, self.abstract_guard_disjuncts[t],
                                                                          self.abstract_effect[t], p))


            # TODO can optimise, since same t may be both env or con
            for t, t_formula, invars, constants, Es, new_effects in results:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_tran_preds_constant[t] += constants
                self.abstract_guard_disjuncts[t] = Es
                self.abstract_effect[t] = new_effects

        end = time.time()
        logger.info(end - start)

        start = time.time()
        # self.prune_predicate_sets()
        # self.prune_based_on_explicit_abstraction()
        end = time.time()
        logger.info(end - start)

        self.transition_predicates += new_transition_predicates

        self.pretty_print_abstract_effect()

        # rename_pred = lambda p: pred_name_dict[p] if p in pred_name_dict.keys() else p

        #
        #
        # logger.info("LTL formula: " + str(ltl))
        # return init_transition_ltl, [X(G(disjunct_formula_set(transition_ltl)))]

    def simplified_transitions_abstraction(self):
        new_env_transitions, env_to_program_transitions = merge_transitions(self.abstraction.transitions,
                                                                            self.program.symbol_table,
                                                                            self.env_to_program_transitions)
        new_con_transitions, con_to_program_transitions = merge_transitions(self.abstraction.con_transitions,
                                                                            self.program.symbol_table,
                                                                            self.con_to_program_transitions)
        self.env_to_program_transitions = env_to_program_transitions
        self.con_to_program_transitions = con_to_program_transitions

        return Program("pred_abst_" + self.abstraction.name, self.abstraction.states, self.abstraction.initial_state,
                       [],
                       new_env_transitions, new_con_transitions, self.abstraction.env_events,
                       self.abstraction.con_events, self.abstraction.out_events, False, preprocess=True)

    def to_automaton_abstraction(self):
        self.abstraction_automaton = effects_to_explicit_automaton_abstraction(self)
        return self.abstraction_automaton

    def get_symbol_table(self):
        return self.symbol_table

    def get_state_predicates(self):
        return self.state_predicates

    def get_transition_predicates(self):
        return self.transition_predicates

    def get_interpolants(self) -> [Formula]:
        return self.interpolants

    def get_ranking_and_invars(self):
        pass

    def get_program(self):
        return self.program

    def massage_mealy_machine(self,
                              mm_hoa: str,
                              base_abstraction,
                              ltlAbstractionType: LTLAbstractionType,
                              synthesis_problem: AbstractLTLSynthesisProblem,
                              controller: bool) -> MealyMachine:
        if ltlAbstractionType.base_type == LTLAbstractionBaseType.explicit_automaton and \
                ltlAbstractionType.transition_type == LTLAbstractionTransitionType.combined and \
                ltlAbstractionType.structure_type == LTLAbstractionStructureType.control_and_predicate_state and \
                ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env:

            mm = parse_hoa(synthesis_problem, output=mm_hoa, env_con_separate=False, abstraction=self)

            if controller:
                return mm
            else:
                return mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(self,
                                                                                                 self.program,
                                                                                                 base_abstraction)
        elif ltlAbstractionType.base_type == LTLAbstractionBaseType.effects_representation and \
                ltlAbstractionType.transition_type == LTLAbstractionTransitionType.env_con_separate and \
                ltlAbstractionType.structure_type == LTLAbstractionStructureType.control_state and \
                ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env:

            mm = parse_hoa(synthesis_problem, output=mm_hoa, env_con_separate=True, abstraction=self)

            return mm
        elif ltlAbstractionType.base_type == LTLAbstractionBaseType.effects_representation and \
            ltlAbstractionType.transition_type == LTLAbstractionTransitionType.one_trans and \
            ltlAbstractionType.structure_type == LTLAbstractionStructureType.control_state and \
            ltlAbstractionType.output_type == LTLAbstractionOutputType.no_output:

            mm = parse_hoa(synthesis_problem, output=mm_hoa, env_con_separate=False, abstraction=self, one_trans=True)

            return mm

        else:
            raise NotImplementedError("Options for LTL abstraction not implemented: " + str(ltlAbstractionType))

    def concretise_counterexample(self, counterexample: [dict]):
        pass


def compute_abstract_effect_with_p_parallel(arg):
    t, Es, old_effects, predicate, symbol_table = arg

    if len(old_effects) == 0:
        return t, transition_formula(t), [], [], Es, old_effects
    # TODO
    #   1. keep track of powersets of preds that are satisfiable with guard
    #   then consider the effects of the actions on the new predicates
    #   2. in the first step we do some optimisation, by not considering predicates with variables unmentioned in
    #   guard and right-hand side of actions
    #   3. in the second step we do some optimisation, by checking whether the variables in the candidate effect
    #   predicate are modified in the actions or not
    #   4. if a predicate truth in the next step cannot be determined, then do not explode effect set, but keep track
    #   in separate set, and try to determine it s truth when new predicates are added

    is_tran_pred = lambda q: any(True for v in q.variablesin() if str(v).endswith("_prev"))

    action = t.action
    # TODO, if no vars modified, then only need need to abstract guards in terms of predicates, then they maintain same value

    vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
    vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in
                                            a.right.variablesin()]

    t_formula = transition_formula(t)

    invars = []
    constants = []
    new_effects = {x: y for x, y in old_effects.items()}

    variable_used_in_guard = any(True for v in predicate.variablesin() if v in t.condition.variablesin())
    value_modified = any(True for v in predicate.variablesin()
                                if v in vars_modified_in_action_without_identity +
                                        vars_used_in_action_without_identity)
    # if the predicate is a state predicate and is not mentioned in both the guard and action
    if not is_tran_pred(predicate) and not variable_used_in_guard and not value_modified:
        invars = [predicate]
        return t, t_formula, invars, constants, Es, new_effects
    # if the predicate is an inc or dec transition predicate and is not mentioned in the action
    elif (is_tran_pred(predicate)
          and isinstance(predicate, BiOp) and predicate.op in ["<", ">"]  # This is only applicable for decs and incs
          and not value_modified):
        constants = [neg(predicate)]
    # if the predicate is always false after the transition
    elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), symbol_table):
        constants = [neg(predicate)]
    # if the predicate is always true after the transition
    elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), symbol_table):
        constants = [(predicate)]
    # if the predicate is maintained by the transition
    elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]),
                          symbol_table) and \
            is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]),
                             symbol_table):
        # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
        invars = [(predicate)]

    action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
    if len(constants) > 0 or len(invars) > 0:
        # TODO optimisation: if no variable in predicate is mentioned in guard,
        #  then just explode the precondition set without any sat checks
        #  Correction: eh, need to consider when predicate is relevant for guard:
        #    if they have variables in common?
        #    if the predicate has variables in common with other relevant predicates?
        #    if not relevant, need to keep track, and consider adding it later
        #    or is there a way to avoid adding later? the only reason to add later would be that a new relevant pred
        #    has vars in common with an irrelevant pred; could we instead try to identify invariant relationships
        #    between the predicates?
        # TODO, don t want to explode before needed, collect all such predicates,
        #  then add iff a new predicate to be added may be affected by the collected predicates
        for (guard_disjunct, E) in Es:
            formula_pos = add_prev_suffix(conjunct(guard_disjunct, predicate))
            formula_pos = conjunct(formula_pos, action_formula)
            if sat(formula_pos, symbol_table):
                try_pos = True
            else:
                try_pos = False

            formula_neg = add_prev_suffix(conjunct(guard_disjunct, neg(predicate)))
            formula_neg = conjunct(formula_neg, action_formula)
            if sat(formula_neg, symbol_table):
                try_neg = True
            else:
                try_neg = False
            newNextPss = InvertibleMap()

            # old_effects[E] is an InvertibleMap
            for (nextPs, Pss) in old_effects[E].items():
                if not relevant_pred(t, nextPs, predicate):
                    # new_effects[E] = old_effects[E]
                    newNextPss.put(nextPs, Pss)
                    continue

                new_pos_Ps = set()
                new_neg_Ps = set()
                for Ps in Pss:
                    # if p was true before, is p possible next?
                    if try_pos and sat(conjunct(conjunct_formula_set(nextPs),
                                                conjunct(formula_pos,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_pos_Ps.add(Ps | {predicate})

                    # if p was false before, is p possible next?
                    if try_neg and sat(conjunct(conjunct_formula_set(nextPs),
                                                conjunct(formula_neg,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_neg_Ps.add(Ps | {neg(predicate)})
                # self.all_pred_states.add(frozenset(new_pos_Ps))
                # self.all_pred_states.add(frozenset(new_neg_Ps))

                new_now = frozenset(P for P in new_neg_Ps | new_pos_Ps)
                if len(new_now) > 0:
                    newNextPss.put(nextPs, new_now)

            if len(newNextPss) > 0:
                new_effects[E] = newNextPss
            else:
                if E in new_effects.keys():
                    new_effects.pop(E)

                Es.remove((guard_disjunct, E))
    else:
        prev_predicate = add_prev_suffix(predicate)
        for (guard_disjunct, E) in Es:
            # E_formula = add_prev_suffix(conjunct_formula_set(E))
            new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))
            formula_pos = conjunct(new_formula, prev_predicate)
            if sat(formula_pos, symbol_table):
                try_pos = True
            else:
                try_pos = False

            formula_neg = conjunct(new_formula, neg(prev_predicate))
            if sat(formula_neg, symbol_table):
                try_neg = True
            else:
                try_neg = False
            newNextPss = InvertibleMap()

            # old_effects[E] is an InvertibleMap
            for (nextPs, Pss) in old_effects[E].items():
                nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                new_pos_Ps = set()
                new_neg_Ps = set()
                for Ps in Pss:
                    # if p was true before, is p possible next?
                    if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                conjunct(formula_pos,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_pos_Ps.add(Ps | {predicate})

                    # if p was false before, is p possible next?
                    if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                conjunct(formula_neg,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_pos_Ps.add(Ps | {neg(predicate)})

                    # if p was true before, is not p possible next?
                    if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                conjunct(formula_pos,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_neg_Ps.add(Ps | {predicate})

                    # if p was false before, is not p possible next?
                    if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                conjunct(formula_neg,
                                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                       symbol_table):
                        new_neg_Ps.add(Ps | {neg(predicate)})

                if len(new_pos_Ps) > 0:
                    newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                if len(new_neg_Ps) > 0:
                    newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

            if len(newNextPss) > 0:
                new_effects[E] = newNextPss
            else:
                if E in new_effects.keys():
                    new_effects.pop(E)

                Es.remove((guard_disjunct, E))
    return t, t_formula, invars, constants, Es, new_effects


def add_transition_predicate_to_t_parallel(arg):
    t, Es, old_effects, predicate, symbol_table = arg
    if len(old_effects) == 0:
        return t, transition_formula(t), [], [], Es, old_effects

    if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
        raise Exception(str(predicate) + " is not a transition predicate.")

    action = t.action

    t_formula = transition_formula(t)

    invars = []
    constants = []
    new_effects = {x: y for x, y in old_effects.items()}
    # if the transition predicate is not mentioned in the action
    if is_contradictory(conjunct_formula_set([t_formula, (predicate)]), symbol_table):
        constants = [neg(predicate)]
    elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), symbol_table):
        constants = [(predicate)]
    # if cannot determine exactly whether to the pred is a constant, then for replicate each post state
    # for each possibility
    else:
        action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
        for (guard_disjunct, E) in Es:
            # E_formula = add_prev_suffix(conjunct_formula_set(E))
            new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))

            newNextPss = InvertibleMap()

            # old_effects[E] is an InvertibleMap
            for (nextPs, Pss) in old_effects[E].items():
                nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                new_pos_Ps = set()
                new_neg_Ps = set()
                for Ps in Pss:
                    if sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                    conjunct(new_formula,
                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                           symbol_table):
                        new_pos_Ps.add(Ps)

                    if sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                    conjunct(new_formula,
                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                           symbol_table):
                        new_neg_Ps.add(Ps)

                if len(new_pos_Ps) > 0:
                    newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                if len(new_neg_Ps) > 0:
                    newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

            if len(newNextPss) > 0:
                new_effects[E] = newNextPss
            else:
                if E in new_effects.keys():
                    new_effects.pop(E)

                Es.remove((guard_disjunct, E))
    return t, t_formula, invars, constants, Es, new_effects


def abstract_guard_explicitly_parallel(arg):
    trans, events, symbol_table = arg
    guard = trans.condition
    vars_in_cond = guard.variablesin()

    if is_conjunction_of_atoms(guard):
        conjuncts = guard.sub_formulas_up_to_associativity()
        cond = []
        env_con_events = set()
        for c in conjuncts:
            if not any(v for v in c.variablesin() if v not in events):
                env_con_events.add(c)
            else:
                cond.append(c)
        E = frozenset(env_con_events)
        int_disjuncts_only_events = [E]
        return trans, [(conjunct_formula_set(cond), E)], int_disjuncts_only_events

    events_in_cond = [e for e in vars_in_cond if e in events]
    powerset = powerset_complete(events_in_cond)
    int_disjuncts_only_events = [E for E in powerset if
                                 sat(conjunct_formula_set(E | {guard}), symbol_table)]

    satisfying_behaviour = int_disjuncts_only_events
    dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
    disjuncts = []
    for E in satisfying_behaviour:
        if not E:
            logger.info("empty E " + str(guard))
        guard_E = guard.replace_vars(lambda x: true() if x in E else false() if neg(x) in E else x)
        try:
            guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
        except Exception as e:
            # TODO what is this exception caused by??
            guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
            logging.info(str(e))
        disjuncts.append((guard_E_simplified, E))
    return trans, disjuncts, dnfed
