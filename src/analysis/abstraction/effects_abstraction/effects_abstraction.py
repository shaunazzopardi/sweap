import logging
import time
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.util.effects_util import merge_transitions, relevant_pred_g_u
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionTransitionType, LTLAbstractionBaseType, \
    LTLAbstractionStructureType, LTLAbstractionType, LTLAbstractionOutputType
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis import parse_hoa
from synthesis.mealy_machine import MealyMachine
from programs.typed_valuation import TypedValuation
from programs.program import Program
from programs.transition import Transition
from programs.util import add_prev_suffix, transition_formula, powerset_complete, guard_update_formula, \
    guard_update_formula_to_guard_update
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    true, false, sat, simplify_formula_with_math, is_contradictory, label_pred, stringify_pred, \
    is_conjunction_of_atoms, sat_parallel

logger = logging.getLogger(__name__)


class EffectsAbstraction(PredicateAbstraction):
    def __init__(self, program: Program):
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_tran_preds_constant = {}

        self.init_conf = None
        self.init_disjuncts = set()
        self.init_gu_to_E = {}
        self.init_state_abstraction = []
        self.second_state_abstraction = []

        self.init_program_trans = None
        self.non_init_program_trans = None

        self.transition_guard_update_to_E = {}
        self.transition_E_to_guard_update = {}
        self.guard_updates = set()

        self.state_predicates = []
        self.transition_predicates = []

        self.interpolants = set()
        self.ltl_constraints = []
        self.loops = []
        self.var_relabellings = {}

        self.program = program
        self.loop_counter = 0

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions(parallelise=True)

        self.symbol_table = {v: tv for v, tv in program.symbol_table.items()}

    def abstract_program_transitions(self, parallelise=True):
        # TODO here get stutter transitions
        #    can treat them specially by considering the work already done for transitions from their state
        orig_transitions, stutter = self.program.complete_transitions_stutter_explicit()

        self.init_program_trans = []

        all_trans = orig_transitions + stutter
        self.init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        init_orig_trans_map = {t: t.add_condition(self.init_conf) for t in all_trans if
                               t.src == self.program.initial_state and sat(conjunct(self.init_conf, t.condition),
                                                                           self.program.symbol_table)}
        self.init_program_trans = list(init_orig_trans_map.values())
        self.non_init_program_trans = all_trans

        all_events = self.program.env_events + self.program.con_events

        no_of_workers = config.workers if parallelise else 1

        arg1 = []
        arg2 = []
        arg3 = []
        for t in all_trans:
            arg1.append(t)
            arg2.append(all_events)
            arg3.append(self.program.symbol_table)
        with Pool(no_of_workers) as pool:
            partial_results = pool.map(abstract_guard_explicitly_simple_parallel, zip(arg1, arg2, arg3))
            results = []
            for i, r in enumerate(partial_results):
                if r is None:
                    new_r = abstract_guard_explicitly_complex_parallel(arg1[i], all_events, self.program.symbol_table)
                    results.append(new_r)
                else:
                    results.append(r)

        results_init = []
        empty_effects = {}
        true_set = {frozenset()}
        empty_effects[frozenset()] = frozenset(true_set)

        for t, disjuncts, formula in results:
            self.transition_guard_update_to_E[t] = {}
            self.transition_E_to_guard_update[t] = {}
            u = t.action
            for g, E in disjuncts:
                gu = guard_update_formula(g, u)
                self.guard_updates.add(gu)
                if gu in self.transition_guard_update_to_E[t].keys():
                    self.transition_guard_update_to_E[t][gu].append(E)
                else:
                    self.transition_guard_update_to_E[t][gu] = [E]

                if E in self.transition_E_to_guard_update[t].keys():
                    self.transition_E_to_guard_update[t][E].append((g, u))
                else:
                    self.transition_E_to_guard_update[t][E] = [(g, u)]

                self.abstract_effect[gu] = empty_effects
                self.abstract_effect_invars[gu] = []
                self.abstract_effect_constant[gu] = []
                self.abstract_effect_tran_preds_constant[gu] = []

            if t in init_orig_trans_map.keys():
                arg1 = [conjunct(guard_E, self.init_conf) for guard_E, _ in disjuncts]
                arg2 = [self.program.symbol_table for i in range(0, len(disjuncts))]
                with Pool(no_of_workers) as pool:
                    disj_res = pool.map(sat_parallel, zip(arg1, arg2))

                for i, res in enumerate(disj_res):
                    if res:
                        g_i, E_i = disjuncts[i]
                        g_init = conjunct(g_i, self.init_conf)
                        gu_init = guard_update_formula(g_init, u)
                        if gu_init in self.init_gu_to_E.keys():
                            self.init_gu_to_E[gu_init].append(E_i)
                        else:
                            self.init_gu_to_E[gu_init] = [E_i]
                        self.init_disjuncts.add((gu_init, t.tgt))
                        self.second_state_abstraction.append([])

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

                newNextPss = {}

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
                        newNextPss[nextPs_with_p] = frozenset(P for P in new_pos_Ps)
                    if len(new_neg_Ps) > 0:
                        newNextPss[nextPs_with_neg_p] = frozenset(P for P in new_neg_Ps)

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    if E in new_effects.keys():
                        new_effects.pop(E)

                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def pretty_print_abstract_effect(self):
        for t, Egu in self.transition_E_to_guard_update.items():
            logging.info(str(t))
            for E, (g, u) in self.abstract_effect[t].keys():
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

        # self.pretty_print_abstract_effect()

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

        for p in new_state_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_state_predicates)):
                    TypedValuation(str(label_pred(p, new_state_predicates)), "bool", true())})

            if sat(conjunct(self.init_conf, p), self.symbol_table):
                self.init_state_abstraction.append(p)
            else:
                self.init_state_abstraction.append(neg(p))

            for i, (gu, _) in enumerate(self.init_disjuncts):
                if sat(conjunct(gu, p), self.symbol_table):
                    self.second_state_abstraction[i].append(p)
                else:
                    self.second_state_abstraction[i].append(neg(p))

        no_of_workers = config.workers if parallelise else 1

        arg1 = []
        arg2 = []
        arg3 = []
        arg4 = []
        arg5 = []
        arg6 = []
        for gu in self.guard_updates:
            g, u = guard_update_formula_to_guard_update(gu)
            arg1.append(g)
            arg2.append(u)
            arg3.append(gu)
            arg4.append(self.abstract_effect[gu])
            arg5.append(new_state_predicates)
            arg6.append(self.program.symbol_table)
        with Pool(no_of_workers) as pool:
            results = pool.map(compute_abstract_effect_for_guard_update, zip(arg1, arg2, arg3, arg4, arg5, arg6))

        for g, u, gu, invars, constants, new_effects in results:
            self.abstract_effect_invars[gu].extend(invars)
            self.abstract_effect_constant[gu].extend(constants)
            self.abstract_effect[gu] = new_effects

        # if config.debug:
        #     # sanity check
        #     for t, E_effects in self.abstract_effect.items():
        #         t_f = transition_formula(t)
        #         for E, next_nows in E_effects.items():
        #             f = conjunct(t_f, add_prev_suffix(conjunct_formula_set(E)))
        #             for next, nows in next_nows.items():
        #                 for now in nows:
        #                     effects_f = disjunct_formula_set([conjunct(conjunct_formula_set(next),
        #                                                        add_prev_suffix(conjunct_formula_set(now)))])
        #                     to_check = conjunct(f, effects_f)
        #                     if not sat(to_check, self.symbol_table):
        #                         raise Exception("something wrong in effectsabsttraction")

        end = time.time()
        logger.info(end - start)

        start = time.time()
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
        for p in new_transition_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_transition_predicates)):
                    TypedValuation(str(label_pred(p, new_transition_predicates)), "bool", true())})

            self.init_state_abstraction.append(neg(p))
            for i, (gu, _) in enumerate(self.init_disjuncts):
                if sat(conjunct(gu, p), self.symbol_table):
                    self.second_state_abstraction[i].append(p)
                else:
                    self.second_state_abstraction[i].append(neg(p))

        no_of_workers = config.workers if parallelise else 1

        arg1 = []
        arg2 = []
        arg3 = []
        arg4 = []
        arg5 = []
        arg6 = []
        for gu in self.guard_updates:
            g, u = guard_update_formula_to_guard_update(gu)
            arg1.append(g)
            arg2.append(u)
            arg3.append(gu)
            arg4.append(self.abstract_effect[gu])
            arg5.append(new_transition_predicates)
            arg6.append(self.program.symbol_table)

        with Pool(no_of_workers) as pool:
            results = pool.map(add_transition_predicates_to_t_guard_updates, zip(arg1, arg2, arg3, arg4, arg5, arg6))

        for g, u, gu, invars, constants, new_effects in results:
            self.abstract_effect_invars[gu] += invars
            self.abstract_effect_tran_preds_constant[gu] += constants
            self.abstract_effect[gu] = new_effects

        end = time.time()
        logger.info(end - start)

        start = time.time()
        end = time.time()
        logger.info(end - start)

        self.transition_predicates += new_transition_predicates

        # self.pretty_print_abstract_effect()

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
        raise NotImplementedError("EffectsAbstraction: to_automaton_abstraction not implemented")

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


def compute_abstract_effect_for_guard_update(arg):
    g, u, gu_formula, old_effects, predicates, symbol_table = arg

    invars = []
    constants = []
    for p in predicates:
        g, u, gu_formula, invars_p, constants_p, effects = (
            compute_abstract_effect_with_p_guard_update((g, u, gu_formula, old_effects, p, symbol_table)))
        old_effects = effects
        invars.extend(invars_p)
        constants.extend(constants_p)

    return g, u, gu_formula, invars, constants, old_effects


def add_transition_predicates_to_t_guard_updates(arg):
    g, u, gu_formula, old_effects, predicates, symbol_table = arg

    invars = []
    constants = []
    for p in predicates:
        g, u, gu_formula, invars_p, constants_p, effects = (
            add_transition_predicate_to_t_guard_updates((g, u, gu_formula, old_effects, p, symbol_table)))
        old_effects = effects
        invars.extend(invars_p)
        constants.extend(constants_p)

    return g, u, gu_formula, invars, constants, old_effects


def compute_abstract_effect_with_p_guard_update(arg):
    g, u, gu_formula, old_effects, predicate, symbol_table = arg

    if len(old_effects) == 0:
        return g, u, gu_formula, [], [], old_effects

    is_tran_pred = lambda q: any(True for v in q.variablesin() if str(v).endswith("_prev"))

    action = u
    # TODO, if no vars modified, then only need need to abstract guards in terms of predicates, then they maintain same value

    vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
    vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in
                                            a.right.variablesin()]

    invars = []
    constants = []
    new_effects = {x: y for x, y in old_effects.items()}

    variable_used_in_guard = any(True for v in predicate.variablesin() if v in g.variablesin())
    value_modified = any(True for v in predicate.variablesin()
                         if v in vars_modified_in_action_without_identity +
                         vars_used_in_action_without_identity)
    # if the predicate is a state predicate and is not mentioned in both the guard and action
    if not is_tran_pred(predicate) and not variable_used_in_guard and not value_modified:
        invars = [predicate]
        return g, u, gu_formula, invars, constants, new_effects
    # if the predicate is an inc or dec transition predicate and is not mentioned in the action
    elif (is_tran_pred(predicate)
          and isinstance(predicate, BiOp) and predicate.op in ["<", ">"]  # This is only applicable for decs and incs
          and not value_modified):
        constants = [neg(predicate)]
    # if the predicate is always false after the transition
    elif is_contradictory(conjunct_formula_set([gu_formula, (predicate)]), symbol_table):
        constants = [neg(predicate)]
    # if the predicate is always true after the transition
    elif is_contradictory(conjunct_formula_set([gu_formula, neg(predicate)]), symbol_table):
        constants = [(predicate)]
    # if the predicate is maintained by the transition
    elif is_contradictory(conjunct_formula_set([gu_formula, add_prev_suffix(predicate), neg(predicate)]),
                          symbol_table) and \
            is_contradictory(conjunct_formula_set([gu_formula, add_prev_suffix(neg(predicate)), (predicate)]),
                             symbol_table):
        # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
        invars = [(predicate)]

    formula_pos = conjunct(gu_formula, add_prev_suffix(predicate))
    if sat(formula_pos, symbol_table):
        try_pos = True
    else:
        try_pos = False

    formula_neg = conjunct(gu_formula, add_prev_suffix(neg(predicate)))
    if sat(formula_neg, symbol_table):
        try_neg = True
    else:
        try_neg = False
    newNextPss = {}

    if len(constants) > 0 or len(invars) > 0:
        # old_effects[E] is an InvertibleMap
        for (nextPs, Pss) in old_effects.items():
            if not relevant_pred_g_u(g, u, nextPs, predicate):
                newNextPss[nextPs] = Pss
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

            new_now = frozenset(P for P in new_neg_Ps | new_pos_Ps)
            if len(new_now) > 0:
                newNextPss[nextPs] = new_now
    else:
        for (nextPs, Pss) in old_effects.items():
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
                newNextPss[nextPs_with_p] = frozenset(P for P in new_pos_Ps)
            if len(new_neg_Ps) > 0:
                newNextPss[nextPs_with_neg_p] = frozenset(P for P in new_neg_Ps)

    new_effects = newNextPss
    return g, u, gu_formula, invars, constants, new_effects


def add_transition_predicate_to_t_guard_updates(arg):
    g, u, gu, old_effects, predicate, symbol_table = arg
    if len(old_effects) == 0:
        return g, u, gu, [], [], old_effects

    if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
        raise Exception(str(predicate) + " is not a transition predicate.")

    action = u

    t_formula = guard_update_formula(g, u)

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
        new_formula = gu

        newNextPss = {}

        for (nextPs, Pss) in old_effects.items():
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
                newNextPss[nextPs_with_p] = frozenset(P for P in new_pos_Ps)
            if len(new_neg_Ps) > 0:
                newNextPss[nextPs_with_neg_p] = frozenset(P for P in new_neg_Ps)

        new_effects = newNextPss
    return g, u, gu, invars, constants, new_effects


def abstract_guard_explicitly_simple_parallel(arg):
    trans, events, symbol_table = arg
    guard = trans.condition

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
    else:
        return None


def abstract_guard_explicitly_complex_parallel(trans, events, symbol_table):
    guard = trans.condition
    vars_in_cond = guard.variablesin()

    events_in_cond = [e for e in vars_in_cond if e in events]
    powerset = powerset_complete(events_in_cond)
    int_disjuncts_only_events = []
    disjuncts = []

    arg1 = []
    arg2 = []
    arg3 = []
    for E in powerset:
        arg1.append(E)
        arg2.append(guard)
        arg3.append(symbol_table)

    with Pool(config.workers) as pool:
        results = pool.map(deal_with_powerset, zip(arg1, arg2, arg3))

    for r in results:
        if r is not None:
            (guard_E, E) = r
            int_disjuncts_only_events.append(E)
            disjuncts.append((guard_E, E))

    dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])

    return trans, disjuncts, dnfed


def deal_with_powerset(arg):
    E, guard, symbol_table = arg

    guard_E = guard.replace_vars(lambda x: true() if x in E else false() if neg(x) in E else x)
    if sat(guard_E, symbol_table):
        try:
            guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
        except Exception as e:
            # TODO what is this exception caused by??
            guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
            logging.info(str(e))
        return guard_E_simplified, E
    else:
        return None


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
    int_disjuncts_only_events = []
    for E in powerset:
        guard = guard.replace_vars(lambda x: true() if x in E else false() if neg(x) in E else x)
        if sat(guard, symbol_table):
            int_disjuncts_only_events.append(E)

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
