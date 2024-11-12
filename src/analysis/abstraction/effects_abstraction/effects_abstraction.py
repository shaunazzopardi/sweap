import logging
import time
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.abs_util import update_var_partition, update_var_partition_mult
from analysis.abstraction.effects_abstraction.predicates import StatePredicate
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import ChainPredicate
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import StatePredicate
from analysis.abstraction.effects_abstraction.predicates.Predicate import Predicate
from analysis.abstraction.effects_abstraction.util.effects_util import merge_transitions, relevant_pred_g_u
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionTransitionType, LTLAbstractionBaseType, \
    LTLAbstractionStructureType, LTLAbstractionType, LTLAbstractionOutputType
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
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
from prop_lang.util import (conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
                            true, false, sat, simplify_formula_with_math, is_contradictory, label_pred, stringify_pred, \
                            is_conjunction_of_atoms, sat_parallel, simplify_formula_without_math, X, iff,
                            strip_mathexpr, propagate_nexts, is_conjunction_of_atoms_modulo_vars, is_tautology,
                            disjunct)

logger = logging.getLogger(__name__)


class EffectsAbstraction(PredicateAbstraction):
    def __init__(self, program: Program):
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_ltl = {}
        self.abstract_effect_tran_preds_constant = {}
        self.abstracted_preds = {} #will keep track of which predicates are abstracted for each gu

        self.partitions = {}
        self.v_to_p = {}
        self.v_to_partition = {}
        self.gu_to_relevant = {}

        self.v_to_chain_pred = {}

        self.init_conf = None
        self.init_disjuncts = []
        self.init_gu_to_E = {}
        self.init_state_abstraction = []
        self.second_state_abstraction = []

        self.init_program_trans = None
        self.non_init_program_trans = None

        self.u_to_gu = {}
        self.trans_to_u = {}
        self.u_constants = {}

        self.transition_guard_update_to_E = {}
        self.transition_E_to_guard_update = {}
        self.guard_updates = set()

        self.wrapped_preds = set()
        self.state_predicates = set()
        self.chain_state_predicates = set()
        self.transition_predicates = set()
        self.chain_rep = {}

        self.current_chain_all_bin_rep = {}
        self.pred_to_v = {}

        self.interpolants = set()
        self.ranking_constraints = {}
        self.structural_loop_constraints = []
        self.loops = []
        self.var_relabellings = {}

        self.program = program
        self.loop_counter = 0

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions(parallelise=True)

        self.symbol_table = {v: tv for v, tv in program.symbol_table.items()}

        # for v in self.symbol_table:
        #     tv = self.symbol_table[v]
        #     if "_prev_" not in str(tv.name) and \
        #         (tv.type.lower().startswith('int') or tv.type.lower().startswith('nat') or ".." in tv.type):
        #         self.chains[Variable(v)] = (([],[],{}), ([],[],{}))

    def abstract_program_transitions(self, parallelise=True):
        # TODO here get stutter transitions
        #    can treat them specially by considering the work already done for transitions from their state
        orig_transitions, stutter = self.program.complete_transitions_stutter_explicit()

        self.init_program_trans = []

        all_trans = orig_transitions + stutter
        self.init_conf = (conjunct_typed_valuation_set(self.program.valuation))
        init_orig_trans_map = {t: t.add_condition(self.init_conf) for t in all_trans if
                               t.src == self.program.initial_state and sat(conjunct(self.init_conf, t.condition),
                                                                           self.program.symbol_table)}
        self.init_program_trans = list(init_orig_trans_map.values())
        self.non_init_program_trans = all_trans

        all_events = self.program.env_events + self.program.con_events

        no_of_workers = config.Config.getConfig().workers if parallelise else 1

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

        # empty_list = list()
        # empty_list.append(list())
        # empty_effects = [(list(), empty_list)]


        init_disjuncts_set = set()

        for t, disjuncts, formula in results:
            self.transition_guard_update_to_E[t] = {}
            self.transition_E_to_guard_update[t] = {}
            U = t.action
            u_f = conjunct_formula_set([BiOp(up.left, "=", add_prev_suffix(up.right)) for up in t.action], sort=True)

            self.trans_to_u[t] = u_f

            for g, E in disjuncts:
                gu = guard_update_formula(g, U, self.program.symbol_table)

                vars_g = set(g.variablesin())
                vars_u = set()
                for u in U:
                    if u.left != u.right:
                        vars_u.add(u.left)
                        vars_g.update(u.right.variablesin())

                self.gu_to_relevant[gu] = (vars_g, vars_u)

                self.abstract_effect_ltl[gu] = true()
                if u_f in self.u_to_gu.keys():
                    self.u_to_gu[u_f].add(gu)
                else:
                    self.u_to_gu[u_f] = {gu}
                if u_f not in self.u_constants.keys():
                    self.u_constants[u_f] = []

                self.guard_updates.add(gu)
                if gu in self.transition_guard_update_to_E[t].keys():
                    self.transition_guard_update_to_E[t][gu].append(E)
                else:
                    self.transition_guard_update_to_E[t][gu] = [E]

                if E in self.transition_E_to_guard_update[t].keys():
                    self.transition_E_to_guard_update[t][E].append((g, U))
                else:
                    self.transition_E_to_guard_update[t][E] = [(g, U)]

                empty_effects = [(true(), [(u, [true()]) for u in U if u.left != u.right])]

                self.abstract_effect[gu] = empty_effects
                self.abstracted_preds[gu] = set()
                self.abstract_effect_invars[gu] = set()
                self.abstract_effect_constant[gu] = set()
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
                        gu_init = guard_update_formula(g_init, U, self.program.symbol_table)
                        if gu_init in self.init_gu_to_E.keys():
                            self.init_gu_to_E[gu_init].append(E_i)
                        else:
                            self.init_gu_to_E[gu_init] = [E_i]
                        init_disjuncts_set.add((gu_init, t.tgt))
        for t in init_disjuncts_set:
            self.init_disjuncts.append(t)
            self.second_state_abstraction.append([])

    def add_transition_predicate_to_t(self, t: Transition, Es, old_effects, predicate):
        if len(old_effects) == 0:
            return t, transition_formula(t), [], [], Es, old_effects

        if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
            raise Exception(str(predicate) + " is not a transition predicate.")

        action = t.action

        t_formula = transition_formula(t)

        invars = set()
        constants = set()
        new_effects = {x: y for x, y in old_effects.items()}
        # if the transition predicate is not mentioned in the action
        if is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table):
            constants = {neg(predicate)}
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table):
            constants = {(predicate)}
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

        self.interpolants.update(new_state_predicates)
        self.add_transition_predicates(new_transition_predicates, parallelise)
        self.add_state_predicates(new_state_predicates, parallelise)

        # self.pretty_print_abstract_effect()

    def add_ranking_constraints(self, new_ranking_constraints: dict[Formula, [Formula]]):
        for dec, constraint in new_ranking_constraints:
            processed_ltl_constraints = []
            processed = strip_mathexpr(constraint.right)
            processed_ltl_constraints.append(processed)
            processed_dec = self.var_relabellings[dec]
            if processed_dec not in self.ranking_constraints.keys():
                self.ranking_constraints[processed_dec] = processed_ltl_constraints
            else:
                self.ranking_constraints[processed_dec].extend(processed_ltl_constraints)

    def add_structural_loop_constraints(self, new_structural_loop_constraints):
        for constraint in new_structural_loop_constraints:
            processed_ltl_constraints = []
            processed = strip_mathexpr(constraint)
            processed_ltl_constraints.append(processed)
            self.structural_loop_constraints.extend(processed_ltl_constraints)

    def add_state_predicates(self, new_state_predicates: [Formula], parallelise=True):
        if len(new_state_predicates) == 0:
            return
        #assuming input state predicates have been normalised (all of type < or <=, and vars on LHS and constants on RHS

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()

        use_chain_preds = True
        remaining_st_preds = new_state_predicates

        new_preds = set()

        if use_chain_preds:
            v_to_p_for_chain = {}
            remaining_st_preds = []
            for p in new_state_predicates:
                p_vars = p.variablesin()
                if not any(v for v in p_vars if "_prev" in p_vars) and not isinstance(p, Variable):
                    if p_vars[0] not in v_to_p_for_chain.keys():
                        v_to_p_for_chain[p_vars[0]] = [p]
                    else:
                        v_to_p_for_chain[p_vars[0]].append(p)
                else:
                    f_p = StatePredicate(p)
                    remaining_st_preds.append(f_p)
                    new_preds.add(f_p)
                    self.state_predicates.add(p)

            for v, preds in v_to_p_for_chain.items():
                self.chain_state_predicates.update(preds)
                new_chain_pred = False
                if v not in self.v_to_chain_pred.keys():
                    v_chain_pred = ChainPredicate(v, self.program)
                    self.v_to_chain_pred[v] = v_chain_pred
                    new_chain_pred = True
                else:
                    v_chain_pred = self.v_to_chain_pred[v]

                v_chain_pred.add_predicate(preds)
                new_preds.add(v_chain_pred)

                self.var_relabellings.update(v_chain_pred.boolean_rep())

                if new_chain_pred:
                    for p in v_chain_pred.tran_preds:
                        self.init_state_abstraction.append(neg(p))

                    for p in v_chain_pred.chain:
                        # TODO if transition pred need to set neg of every pred
                        if sat(conjunct(self.init_conf, p), self.symbol_table):
                            self.init_state_abstraction.append(p)
                            break

                    for i, (gu, _) in enumerate(self.init_disjuncts):
                        for p in v_chain_pred.tran_preds:
                            if sat(conjunct(gu, p), self.symbol_table):
                                self.second_state_abstraction[i].append(p)
                            else:
                                self.second_state_abstraction[i].append(neg(p))

                        for p in v_chain_pred.chain:
                            if sat(conjunct(gu, p), self.symbol_table):
                                self.second_state_abstraction[i].append(p)
                                break
                else:
                    old_to_new = v_chain_pred.old_to_new
                    for old_p in old_to_new.keys():
                        # TODO if transition pred do not update
                        if old_p in self.init_state_abstraction:
                            self.init_state_abstraction.remove(old_p)
                            for p in old_to_new[old_p]:
                                if sat(conjunct(self.init_conf, p), self.symbol_table):
                                    self.init_state_abstraction.append(p)
                                    break

                    for i, (gu, _) in enumerate(self.init_disjuncts):
                        for old_p in old_to_new.keys():
                            if old_p in self.second_state_abstraction[i]:
                                self.second_state_abstraction[i].remove(old_p)
                                for p in old_to_new[old_p]:
                                    if sat(conjunct(gu, p), self.symbol_table):
                                        self.second_state_abstraction[i].append(p)
                                        break

        self.partitions, self.v_to_p, self.v_to_partition = \
            update_var_partition_mult(new_preds, self.partitions, self.v_to_p, self.v_to_partition)

        for p in remaining_st_preds:
            self.var_relabellings |= p.boolean_rep()

            self.symbol_table.update({
                str(label_pred(p, new_state_predicates)):
                    TypedValuation(str(label_pred(p, new_state_predicates)), "bool", true())})

            if any(v for v in p.variablesin() if str(v).endswith("_prev")):
                self.init_state_abstraction.append(neg(p.pred))
            elif sat(conjunct(self.init_conf, p.pred), self.symbol_table):
                self.init_state_abstraction.append(p.pred)
            else:
                self.init_state_abstraction.append(neg(p.pred))

            for i, (gu, _) in enumerate(self.init_disjuncts):
                if sat(conjunct(gu, p.pred), self.symbol_table):
                    self.second_state_abstraction[i].append(p.pred)
                else:
                    self.second_state_abstraction[i].append(neg(p.pred))

        no_of_workers = config.Config.getConfig().workers if parallelise else 1

        gs = []
        us = []
        gus = []
        gu_invars = []
        gu_constants = []
        gu_tran_preds_constants = []
        gu_effects = []
        curr_preds = []
        new_predss = []
        rel_vars = []
        partitions = []
        v_to_preds = []
        v_to_partitions = []
        relabelling = []
        symbol_tables = []
        for gu in self.guard_updates:
            g, u = guard_update_formula_to_guard_update(gu)
            gs.append(g)
            us.append(u)
            gus.append(gu)
            gu_invars.append(self.abstract_effect_invars[gu])
            gu_constants.append(self.abstract_effect_constant[gu])
            gu_tran_preds_constants.append(self.abstract_effect_tran_preds_constant[gu])
            gu_effects.append(self.abstract_effect[gu])
            curr_preds.append(self.abstracted_preds[gu])
            new_predss.append(new_preds)
            partitions.append(self.partitions)
            v_to_preds.append(self.v_to_p)
            v_to_partitions.append(self.v_to_partition)
            rel_vars.append(self.gu_to_relevant[gu])
            relabelling.append(self.var_relabellings)
            symbol_tables.append(self.symbol_table)
        with Pool(no_of_workers) as pool:
            results = pool.map(compute_abstract_effect_for_guard_update,
                               zip(gs, us, gus, gu_invars, gu_constants, gu_tran_preds_constants, gu_effects,
                                   curr_preds, new_predss, rel_vars, partitions, v_to_preds, v_to_partitions,
                                   relabelling, symbol_tables))

        for g, u, gu, invars, constants, new_effects, new_curr_preds, bookkeeping, gu_ltl in results:
            (init_nows, init_nexts, pres, posts) = bookkeeping
            for p in init_nows:
                actual_p = self.v_to_chain_pred[p.variablesin()[0]]
                actual_p.init_now.add(gu)
            for p in init_nexts:
                actual_p = self.v_to_chain_pred[p.variablesin()[0]]
                actual_p.init_next.add(gu)
            for p, pre in pres.items():
                actual_p = self.v_to_chain_pred[p.variablesin()[0]]
                if gu in p.last_pre.keys():
                    if p.last_pre[gu] not in constants:
                        print()
                    else:
                        constants.remove(p.last_pre[gu])
                actual_p.last_pre.update({gu: pre})
                constants.append(pre)
            for p, post in posts.items():
                actual_p = self.v_to_chain_pred[p.variablesin()[0]]
                if gu in p.last_post.keys():
                    if p.last_post[gu] not in constants:
                        print()
                    else:
                        constants.remove(p.last_post[gu])
                actual_p.last_post.update({gu: post})
                constants.append(post)

            self.abstract_effect_invars[gu].update({p for p in invars if not isinstance(p, ChainPredicate)})
            self.abstract_effect_invars[gu].update({self.v_to_chain_pred[p.variablesin()[0]] for p in invars if isinstance(p, ChainPredicate)})
            self.abstract_effect_constant[gu].update(constants)
            self.abstract_effect[gu] = new_effects
            self.abstract_effect_ltl[gu] = gu_ltl
            self.abstracted_preds[gu] = {self.v_to_chain_pred[p.variablesin()[0]] for p in new_curr_preds if isinstance(p, ChainPredicate)}
            self.abstracted_preds[gu] |= {p for p in new_curr_preds if isinstance(p, StatePredicate)}

        end = time.time()
        logger.info(end - start)

    def add_transition_predicates(self, new_transition_predicates: [Formula],
                                  parallelise=True):
        if len(new_transition_predicates) == 0:
            return

        for p in new_transition_predicates:
            self.var_relabellings[p] = stringify_pred(p)
            self.var_relabellings[neg(p)] = neg(stringify_pred(p))

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

        no_of_workers = config.Config.getConfig().workers if parallelise else 1

        arg1 = []
        arg2 = []
        arg3 = []
        for u_f in self.u_to_gu.keys():
            for p in new_transition_predicates:
                arg1.append(u_f)
                arg2.append(p)
                arg3.append(self.program.symbol_table)
        with Pool(no_of_workers) as pool:
            results = pool.map(add_transition_predicate_to_update, zip(arg1, arg2, arg3))

        residuals = {}

        for i, result in enumerate(results):
            success, res = result
            u_f = arg1[i]
            if success:
                _, constants = res
                self.u_constants[u_f].extend(constants)
            else:
                if u_f in residuals.keys():
                    residuals[u_f].append(arg2[i])
                else:
                    residuals[u_f] = [arg2[i]]

        arg3 = []
        arg4 = []
        arg5 = []
        arg6 = []
        for u, preds in residuals.items():
            for gu in self.u_to_gu[u]:
                arg3.append(gu)
                arg4.append(self.abstract_effect[gu])
                arg5.append(preds)
                arg6.append(self.program.symbol_table)

        with Pool(no_of_workers) as pool:
            results = pool.map(add_transition_predicates_to_t_guard_updates, zip(arg3, arg4, arg5, arg6))

        for gu, invars, constants, new_effects in results:
            self.abstract_effect_invars[gu] |= invars
            self.abstract_effect_tran_preds_constant[gu] |= constants
            self.abstract_effect[gu] = new_effects

        end = time.time()
        logger.info(end - start)

        start = time.time()
        end = time.time()
        logger.info(end - start)

        self.transition_predicates.update(new_transition_predicates)

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

def compute_nexts(now, nexts, new_next_preds, symbol_table):
    new_nexts = []
    for v, next in nexts:
        if v in new_next_preds.keys():
            new_next_preds_v = new_next_preds[v]
            if len(new_next_preds_v) == 0:
                new_nexts.append((v, next))
            else:
                v_next = []
                for (next_p, next_neg_p) in new_next_preds:
                    next_p = conjunct(next, next_p)
                    next_neg_p = conjunct(next, next_neg_p)

                    if sat(conjunct(now, next_p), symbol_table):
                        v_next.append(next_p)
                    if sat(conjunct(now, next_neg_p), symbol_table):
                        v_next.append(next_neg_p)

                new_nexts.append((v, v_next))
    return new_nexts


def compute_abstract_effect_for_guard_update_old(arg):
    (g, u, gu_formula, curr_now_preds, curr_next_preds, V_g, V_u, partition, v_to_partition,
     v_to_p, v_to_chain, old_effects, symbol_table) = arg

    new_effects = []
    new_now_preds = [(p, neg(p)) for v in V_g for p in v_to_p[v] if p not in curr_now_preds]
    new_next_preds = {v: [(p, neg(p)) for p in v_to_p[v] if p not in curr_next_preds] for v in V_u}

    for now, nexts in old_effects:
        if len(new_now_preds) == 0:
            if len(new_next_preds) == 0:
                new_effects.append((now, nexts))
            else:
                new_effects.append((now, compute_nexts(now, nexts, new_next_preds, symbol_table)))
        else:
            for (p, neg_p) in new_now_preds:
                now_p = conjunct(now, add_prev_suffix(p))
                if sat(now_p, symbol_table):
                    if len(new_next_preds) == 0:
                        new_effects.append((now_p, nexts))
                    else:
                        new_effects.append((now_p, compute_nexts(now_p, nexts, new_next_preds, symbol_table)))

                now_neg_p = conjunct(now, add_prev_suffix(neg_p))
                if sat(now_neg_p, symbol_table):
                    if len(new_next_preds) == 0:
                        new_effects.append((now_neg_p, nexts))
                    else:
                        new_effects.append((now_neg_p, compute_nexts(now_neg_p, nexts, new_next_preds, symbol_table)))

    return new_effects

def update_constants_invars_chain_pre(p: ChainPredicate, gu, symbol_table, constants):
    if gu in p.last_pre.keys():
        last_pre = p.last_pre[gu]
        new_pre, _ = p.refine_old_post_or_pre_cond(last_pre, gu, symbol_table)
        if new_pre is None:
            constants.remove(last_pre)
            return False, None
        else:
            if last_pre != new_pre:
                if last_pre not in constants:
                    print()
                else:
                    constants.remove(last_pre)
                constants.add(new_pre)
            return True, new_pre

    return False, None


def update_constants_invars_chain_post(p: ChainPredicate, gu, symbol_table, constants):
    if gu in p.last_post.keys():
        last_post = p.last_post[gu]
        new_post, _ = p.refine_old_post_or_pre_cond(last_post, gu, symbol_table)
        if new_post is None:
            constants.remove(last_post)
            return False, None
        else:
            if last_post != new_post:
                if last_post not in constants:
                    print()
                else:
                    constants.remove(last_post)
                constants.add(new_post)
            return True, new_post

    return False, None

def update_invars(p: Predicate, gu, symbol_table, invars, constants):
    if isinstance(p, ChainPredicate):
        if p in invars:
            invars.remove(p)
            invars.add(p)
            return True
        else:
            x = p.is_invar(gu, symbol_table)
            if x is not None:
                invars.add(x)
                return True
    else:
        x = p.is_invar(gu, symbol_table)
        if x is not None:
            invars.add(x)
            return True
    return False

def update_pre(p: Predicate, gu, symbol_table, constants):
    if isinstance(p, ChainPredicate):
        result, pre = update_constants_invars_chain_pre(p, gu, symbol_table, constants)
        if result:
            return True, pre
        else:
            x = p.is_pre_cond(gu, symbol_table)
            if x is not None:
                constants.add(x)
                return True, x
    else:
        x = p.is_pre_cond(gu, symbol_table)
        if x is not None:
            constants.add(x)
            return True, x

    return False, None

def update_post(p: Predicate, gu, symbol_table, constants):
    if isinstance(p, ChainPredicate):
        result, post = update_constants_invars_chain_post(p, gu, symbol_table, constants)
        if result:
            return True, post
        else:
            x = p.is_post_cond(gu, symbol_table)
            if x is not None:
                new_post = x
                constants.add(new_post)
                return True, new_post
    else:
        x = p.is_post_cond(gu, symbol_table)
        if x is not None:
            new_post = x
            constants.add(new_post)
            return True, new_post
    return False, None


def fully_determined_guard(guard, effects, constants, symbol_table):
    pres = conjunct_formula_set(p for p in constants if isinstance(p, Variable) or (isinstance(p, UniOp) and isinstance(p.right, Variable)))
    return is_tautology(iff(guard, conjunct(pres, disjunct_formula_set(now_nexts[0] for now_nexts in effects))), symbol_table)


def compute_abstract_effect_for_guard_update(arg):
    (g, u, gu, invars, constants, tran_preds_constants, effects, curr_preds, new_preds, (vars_g, vars_u),
    partitions, v_to_preds, v_to_partition, vars_relabelling, symbol_table) = arg
    # assuming extended chain predicates are removed from curr_preds
    # TODO optimisation, if tran pred from structural refinement, and no updates where it may or may not match, then only abstract in next
    relevant_vars_g = [vv for v in vars_g if v in v_to_partition.keys() for vv in partitions[v_to_partition[v]]]
    preds_to_add_now = {p for v in relevant_vars_g for p in v_to_preds[v]
                        if (isinstance(p, StatePredicate) and p not in curr_preds) or
                        (isinstance(p, ChainPredicate) and (p not in curr_preds or p in new_preds))}

    tran_preds = {p for p in new_preds if isinstance(p, StatePredicate) and "_prev" in str(p.pred)}
    curr_preds = curr_preds.difference(tran_preds)
    preds_to_add_next = {p for v in vars_u if v in v_to_preds.keys() for p in v_to_preds[v]
                         if (isinstance(p, StatePredicate) and p not in curr_preds) or
                         (isinstance(p, ChainPredicate) and (p not in curr_preds or p in new_preds))}

    preds_to_add_next |= tran_preds
    preds_to_add = preds_to_add_now | preds_to_add_next
    new_curr_preds = curr_preds | preds_to_add

    unused_new_preds = new_preds.copy()
    unused_new_preds.difference_update(preds_to_add)
    for p in unused_new_preds:
        if isinstance(p, ChainPredicate):
            if p in invars:
                # an old version/copy of p may be in invars
                invars.remove(p)
            invars.add(p)
        else:
            invars.add(p.bool_var)

    init_nows = []
    init_nexts = []
    pres = {}
    posts = {}

    common_preds = preds_to_add_now.intersection(preds_to_add_next)
    if len(common_preds) > 0:
        for p in common_preds:
            if not update_invars(p, gu, symbol_table, invars, constants):
                if (res := update_pre(p, gu, symbol_table, constants))[0]:
                    if isinstance(p, ChainPredicate):
                        pres[p] = res[1]
                    if not (res := update_post(p, gu, symbol_table, constants))[0]:
                        effects = p.extend_effect_next(gu, effects, symbol_table)
                        if isinstance(p, ChainPredicate):
                            init_nexts.append(p)
                    else:
                        if isinstance(p, ChainPredicate):
                            posts[p] = res[1]
                elif (res := update_post(p, gu, symbol_table, constants))[0]:
                    if isinstance(p, ChainPredicate):
                        posts[p] = res[1]
                    effects = p.extend_effect_now(gu, effects, symbol_table)
                    if isinstance(p, ChainPredicate):
                        init_nows.append(p)
                else:
                    effects = p.extend_effect(gu, effects, symbol_table)
                    if isinstance(p, ChainPredicate):
                        init_nows.append(p)
                        init_nexts.append(p)


        preds_to_add_now.difference_update(common_preds)
        preds_to_add_next.difference_update(common_preds)

    for p in preds_to_add_now:
        if not (res := update_pre(p, gu, symbol_table, constants))[0]:
            effects = p.extend_effect_now(gu, effects, symbol_table)
        else:
            if isinstance(p, ChainPredicate):
                pres[p] = res[1]
        if isinstance(p, ChainPredicate):
            init_nows.append(p)
            if p in invars:
                invars.remove(p)
            invars.add(p)
        else:
            invars.add(p.bool_var)
    for p in preds_to_add_next:
        if not (res := update_post(p, gu, symbol_table, constants))[0]:
            effects = p.extend_effect_next(gu, effects, symbol_table)
            if isinstance(p, ChainPredicate):
                init_nexts.append(p)
        else:
            if isinstance(p, ChainPredicate):
                posts[p] = res[1]

    gu_ltl = []
    # concrete_guard = false()
    for now, nexts in effects:
        E_now = now.replace_formulas(vars_relabelling)
        # concrete_guard = disjunct(concrete_guard, now)

        if len(nexts) == 0:
            gu_ltl.append(E_now)
        else:
            next_conjuncts = []
            for _, v_nexts in nexts:
                if len(v_nexts) == 1 and v_nexts[0] == true():
                    continue
                next_conjuncts.append(disjunct_formula_set([v_next.replace_formulas(vars_relabelling) for v_next in v_nexts]))

            if len(next_conjuncts) == 0:
                gu_ltl.append(E_now)
            else:
                E_next = conjunct_formula_set(next_conjuncts)
                gu_ltl.append(conjunct(E_now, propagate_nexts(X(E_next))))

    gu_ltl = disjunct_formula_set(gu_ltl)
    invar_preds_effects = set()
    for p in set(invars):
        if isinstance(p, ChainPredicate):
            invar_preds_effects.update(iff(b, X(b)) for b in p.bin_vars)
        else:
            if "prev" not in str(p):
                invar_preds_effects.add(iff(p, X(p)))

    constant_effects = []
    new_constants = []
    for p in set(constants):
        new_constants.append(p)
        constant_effects.append(propagate_nexts(p.replace_formulas(vars_relabelling)))

    constants = new_constants

    for p in set(tran_preds_constants):
        constant_effects.append(p.replace_formulas(vars_relabelling))

    gu_ltl = conjunct_formula_set([gu_ltl] + list(invar_preds_effects) + constant_effects)

    return g, u, gu, invars, constants, effects, new_curr_preds, (init_nows, init_nexts, pres, posts), str(gu_ltl)


def compute_abstract_effect_with_p_guard_update(arg):
    g, u, gu_formula, old_effects, predicate, symbol_table, ignore_invar_constants = arg

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

    if not ignore_invar_constants:
        variable_used_in_guard = any(True for v in predicate.variablesin() if v in g.variablesin())
        value_modified = any(True for v in predicate.variablesin()
                             if v in vars_modified_in_action_without_identity +
                             vars_used_in_action_without_identity)
        # if the predicate is a state predicate and is not mentioned in both the guard and action
        if not is_tran_pred(predicate) and not value_modified:
            # TODO add these predicates to guard lazily, only when needed
            invars = [predicate]
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
    newNextPss = []

    if len(constants) > 0 or len(invars) > 0:
        # old_effects[E] is an InvertibleMap
        for (nextPs, Pss) in old_effects:
            if not relevant_pred_g_u(g, u, nextPs, predicate):
                newNextPss.append((nextPs, Pss))
                continue

            new_pos_Ps = []
            new_neg_Ps = []
            next_f = conjunct_formula_set(nextPs)
            for Ps in Pss:
                f_pos = formula_pos
                f_neg = formula_neg
                # if p was true before, is p possible next?
                if try_pos and sat(conjunct(next_f,
                                            conjunct(f_pos,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_pos_Ps.append(Ps + [predicate])

                # if p was false before, is p possible next?
                if try_neg and sat(conjunct(next_f,
                                            conjunct(f_neg,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_neg_Ps.append(Ps + [neg(predicate)])

            new_Ps = new_pos_Ps + new_neg_Ps
            if len(new_Ps) > 0:
                newNextPss.append((nextPs, new_Ps))
    else:
        for (nextPs, Pss) in old_effects:
            nextPs_with_p = [p for p in nextPs]
            nextPs_with_p.append(predicate)
            nextPs_with_neg_p = [p for p in nextPs]
            nextPs_with_neg_p.append(neg(predicate))

            new_pos_Ps = []
            new_neg_Ps = []
            next_f_p = conjunct_formula_set(nextPs_with_p)
            next_f_neg_p = conjunct_formula_set(nextPs_with_neg_p)
            for (Ps) in Pss:
                # if p was true before, is p possible next?
                if try_pos and sat(conjunct(next_f_p,
                                            conjunct(formula_pos,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_pos_Ps.append(Ps + [predicate])

                # if p was false before, is p possible next?
                if try_neg and sat(conjunct(next_f_p,
                                            conjunct(formula_neg,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_pos_Ps.append(Ps + [neg(predicate)])

                # if p was true before, is not p possible next?
                if try_pos and sat(conjunct(next_f_neg_p,
                                            conjunct(formula_pos,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_neg_Ps.append(Ps + [predicate])

                # if p was false before, is not p possible next?
                if try_neg and sat(conjunct(next_f_neg_p,
                                            conjunct(formula_neg,
                                                     conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                   symbol_table):
                    new_neg_Ps.append(Ps + [neg(predicate)])

            if len(new_pos_Ps) > 0:
                newNextPss.append((nextPs_with_p, new_pos_Ps))
            if len(new_neg_Ps) > 0:
                newNextPss.append((nextPs_with_neg_p, new_neg_Ps))

    new_effects = newNextPss
    return g, u, gu_formula, invars, constants, new_effects


def old_preds_to_new(new_i, chain):
    chain_length = len(chain)
    new_pred = chain[new_i]
    if chain_length == 1:
        return {true(): [new_pred, neg(new_pred)]}
    if new_i == 0:
        old_first = chain[1]
        return {old_first: [new_pred, conjunct(neg(new_pred), old_first)]}
    elif new_i == chain_length - 1:
        old_last = chain[new_i - 1]
        return {neg(old_last): [conjunct(neg(old_last), new_pred), neg(new_pred)]}
    else:
        old_i = chain[new_i + 1]
        old_i_minus_1 = chain[new_i - 1]
        return {conjunct(neg(old_i_minus_1), old_i): [conjunct(neg(old_i_minus_1), new_pred), conjunct(neg(new_pred), old_i)]}


def update_state_with_new_chain_preds(old_to_new_preds, Ps):
    new_Pss = []
    if isinstance(old_to_new_preds, list):
        for p in old_to_new_preds:
            new_Pss.append(Ps + [p])
    else:
        # this should be a set of size 1
        common = set(Ps).intersection(old_to_new_preds.keys())
        if len(common) == 0:
            new_Pss.append(Ps)
        else:
            Ps_without_old_p = [p for p in Ps if p not in common]
            for old_p in common:
                for p in old_to_new_preds[old_p]:
                    new_Pss.append(Ps_without_old_p + [p])

    return new_Pss

def add_transition_predicates_to_t_guard_updates(arg):
    gu_formula, old_effects, predicates, symbol_table = arg

    invars = []
    constants = []
    for p in predicates:
        if str(p) in str(gu_formula):
            constants.append(p)
            continue
        gu_formula, invars_p, constants_p, effects = (
            add_transition_predicate_to_t_guard_updates((gu_formula, old_effects, p, symbol_table)))
        old_effects = effects
        invars.extend(invars_p)
        constants.extend(constants_p)

    return gu_formula, invars, constants, old_effects


def add_transition_predicate_to_t_guard_updates(arg):
    gu, old_effects, predicate, symbol_table = arg
    if len(old_effects) == 0:
        return gu, [], [], old_effects

    if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
        raise Exception(str(predicate) + " is not a transition predicate.")

    t_formula = gu

    invars = []
    constants = []
    new_effects = [(x, y) for x, y in old_effects]
    # if the transition predicate is not mentioned in the action
    if is_contradictory(conjunct_formula_set([t_formula, (predicate)]), symbol_table):
        constants = [neg(predicate)]
    elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), symbol_table):
        constants = [(predicate)]
    # if cannot determine exactly whether to the pred is a constant, then for replicate each post state
    # for each possibility
    else:
        new_formula = gu

        newNextPss = []

        for (nextPs, Pss) in old_effects:
            nextPs_with_p = [p for p in nextPs + [predicate]]
            nextPs_with_neg_p = [p for p in nextPs + [neg(predicate)]]
            new_pos_Ps = []
            new_neg_Ps = []
            for Ps in Pss:
                if sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                conjunct(new_formula,
                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                       symbol_table):
                    new_pos_Ps.append(Ps)

                if sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                conjunct(new_formula,
                                         conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                       symbol_table):
                    new_neg_Ps.append(Ps)

            if len(new_pos_Ps) > 0:
                newNextPss.append((nextPs_with_p, new_pos_Ps))
            if len(new_neg_Ps) > 0:
                newNextPss.append((nextPs_with_neg_p, new_neg_Ps))

        new_effects = newNextPss
    return gu, invars, constants, new_effects


def add_transition_predicate_to_update(arg):
    u_f, predicate, symbol_table = arg

    if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
        raise Exception(str(predicate) + " is not a transition predicate.")

    action = (u_f)
    # if the transition predicate is not mentioned in the action
    if is_contradictory(conjunct_formula_set([action, (predicate)]), symbol_table):
        return True, (u_f, [neg(predicate)])
    elif is_contradictory(conjunct_formula_set([action, neg(predicate)]), symbol_table):
        return True, (u_f, [(predicate)])
    else:
        return False, None


def abstract_guard_explicitly_simple_parallel(arg):
    trans, events, symbol_table = arg
    guard = trans.condition

    if is_conjunction_of_atoms_modulo_vars(guard, events):
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
        return trans, [(conjunct_formula_set(cond), E)], conjunct_formula_set(int_disjuncts_only_events)
    elif isinstance(guard, BiOp) and guard.op[0] == "|" \
                and not any(v for v in guard.variablesin() if v in events):
        disjuncts = guard.sub_formulas_up_to_associativity()
        E = frozenset()
        return trans, [(d, E) for d in disjuncts], true()
    elif not any(v for v in guard.variablesin() if v not in events):
        return trans, [(true(), frozenset({guard}))], guard
    else:
        return None


def abstract_guard_explicitly_complex_parallel(trans, events, symbol_table):
    guard = trans.condition
    vars_in_cond = guard.variablesin()

    events_in_cond = [e for e in vars_in_cond if e in events]
    powerset = powerset_complete(events_in_cond)
    int_disjuncts_only_events = []

    arg1 = []
    arg2 = []
    arg3 = []
    for E in powerset:
        arg1.append(E)
        arg2.append(guard)
        arg3.append(symbol_table)

    with Pool(config.Config.getConfig().workers) as pool:
        results = pool.map(deal_with_powerset, zip(arg1, arg2, arg3))

    disjuncts = {}
    for r in results:
        if r is not None:
            (guard_E, E) = r
            int_disjuncts_only_events.append(E)
            if guard_E in disjuncts.keys():
                disjuncts[guard_E].append(conjunct_formula_set(E))
            else:
                disjuncts[guard_E] = [conjunct_formula_set(E)]

    dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])

    return trans, [(g, frozenset({disjunct_formula_set(E)})) for g, E in disjuncts.items()], dnfed


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
