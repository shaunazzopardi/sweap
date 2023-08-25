import itertools
import logging
import time

from programs.abstraction.effects_abstraction.util.InvertibleMap import InvertibleMap
from programs.abstraction.effects_abstraction.util.effects_to_automaton import effects_to_explicit_automaton_abstraction
from programs.abstraction.effects_abstraction.util.effects_util import merge_transitions, relevant_pred
from programs.abstraction.explicit_abstraction.explicit_to_ltl import abstract_ltl_problem
from programs.abstraction.interface.ltl_abstraction_type import LTLAbstractionTransitionType, LTLAbstractionBaseType, \
    LTLAbstractionStructureType, LTLAbstractionType, LTLAbstractionOutputType
from programs.abstraction.interface.predicate_abstraction import PredicateAbstraction
from programs.synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from programs.synthesis.mealy_machine import MealyMachine
from programs.typed_valuation import TypedValuation

logger = logging.getLogger(__name__)

from joblib import Parallel, delayed

from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import add_prev_suffix, transition_formula, powerset_complete, label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    true, false, sat, \
    simplify_formula_with_math, is_contradictory


class EffectsAbstraction(PredicateAbstraction):
    def __init__(self, program: Program):
        self.formula_to_trans = {}
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_relevant_preds = {}
        self.abstract_effect_irrelevant_preds = {}
        self.abstract_effect_tran_preds_constant = {}
        self.all_pred_states = set()
        self.base_abstraction = None
        self.con_env_transitions = {}

        self.init_program_trans = None
        self.abstract_guard_con = None
        self.abstract_guard_con_disjuncts = None
        self.abstract_guard_env = None
        self.abstract_guard_env_disjuncts = None
        self.state_predicates = []
        self.transition_predicates = []

        self.interpolants = set()
        self.ranking_and_invars = {}
        self.loops = []

        self.con_to_program_transitions = None
        self.env_to_program_transitions = None

        self.con_program_transitions_to_abstract = None
        self.env_program_transitions_to_abstract = None

        self.state_to_env_transitions = None
        self.state_to_con_transitions = None

        self.abstraction = None
        self.program = program
        self.cache = {}
        self.f_cache = {}
        self.loop_counter = 0
        self.loops = []

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions()

        # Formula -> (P -> [P])
        for t in self.all_program_trans:
            disjuncts = self.abstract_guard_env_disjuncts[t] if t in self.abstract_guard_env_disjuncts.keys() else \
                self.abstract_guard_con_disjuncts[t]

            formula = transition_formula(t)
            self.formula_to_trans[formula] = t
            self.abstract_effect_invars[t] = []
            self.abstract_effect_constant[t] = []
            self.abstract_effect_tran_preds_constant[formula] = []

        self.symbol_table = {v:tv for v, tv in program.symbol_table.items()}

    def abstract_program_transition_env(self, env_trans: Transition, symbol_table):
        disjuncts, formula = self.abstract_guard(env_trans.condition, self.program.env_events, symbol_table)
        return env_trans, disjuncts, formula

    def abstract_program_transition_con(self, con_trans: Transition, symbol_table):
        disjuncts, formula = self.abstract_guard(con_trans.condition, self.program.con_events, symbol_table)
        return con_trans, disjuncts, formula

    def abstract_program_transitions(self, parallelise=True):
        # TODO here get stutter transitions
        #    can treat them specially by considering the work already done for transitions from their state
        orig_env_transitions, orig_con_transitions, stutter_env, stutter_cons = self.program.complete_transitions_stutter_explicit()

        self.abstract_guard_env = {}
        self.abstract_guard_con = {}
        self.abstract_guard_env_disjuncts = {}
        self.abstract_guard_con_disjuncts = {}

        self.init_program_trans = []

        if parallelise:
            n_jobs = -1
        else:
            n_jobs = 1

        results_env = Parallel(n_jobs=n_jobs, prefer="threads", verbose=11)(
            delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in
            orig_env_transitions + stutter_env)
        init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        self.init_program_trans = [t.add_condition(init_conf) for t in orig_env_transitions + stutter_env if
                                   t.src == self.program.initial_state and sat(conjunct(init_conf, t.condition),
                                                                               self.program.symbol_table)]
        results_init = Parallel(n_jobs=n_jobs, prefer="threads", verbose=11)(
            delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in
            self.init_program_trans)
        results_con = Parallel(n_jobs=n_jobs, prefer="threads", verbose=11)(
            delayed(self.abstract_program_transition_con)(t, self.program.symbol_table) for t in
            orig_con_transitions + stutter_cons)

        for t, disjuncts, formula in results_env + results_init:
            self.abstract_guard_env[t] = formula
            self.abstract_guard_env_disjuncts[t] = disjuncts
            empty_effects = InvertibleMap()
            true_set = {frozenset()}
            empty_effects.put(frozenset(), frozenset(true_set))
            self.abstract_effect[t] = {E: empty_effects for _, E in disjuncts}
            self.abstract_effect_relevant_preds[t] = {E: set() for _, E in disjuncts}
            self.abstract_effect_irrelevant_preds[t] = {E: set() for _, E in disjuncts}

        for t, disjuncts, formula in results_con:
            self.abstract_guard_con[t] = formula
            self.abstract_guard_con_disjuncts[t] = disjuncts
            empty_effects = InvertibleMap()
            true_set = {frozenset()}
            empty_effects.put(frozenset(), frozenset(true_set))
            self.abstract_effect[t] = {E: empty_effects for _, E in disjuncts}
            self.abstract_effect_relevant_preds[t] = {E: set() for _, E in disjuncts}
            self.abstract_effect_irrelevant_preds[t] = {E: set() for _, E in disjuncts}

        self.all_program_trans = orig_env_transitions + orig_con_transitions + self.init_program_trans + stutter_env + stutter_cons

    def abstract_guard_explicitly(self, guard, events, symbol_table):
        vars_in_cond = guard.variablesin()
        events_in_cond = [e for e in vars_in_cond if e in events]
        powerset = powerset_complete(events_in_cond)

        solver = SMTChecker()

        int_disjuncts_only_events = [E for E in powerset if
                                     sat(conjunct_formula_set(E | {guard}), self.program.symbol_table, solver)]

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
                print(str(e))
            disjuncts.append((guard_E_simplified, E))
        return disjuncts, dnfed

    def abstract_guard(self, guard: Formula, events, symbol_table, use_set_method=True):
        return self.abstract_guard_explicitly(guard, events, symbol_table)

    def compute_abstract_effect_with_p(self, t: Transition, Es, old_effects, predicate):
        if len(old_effects) == 0:
            return t, transition_formula(t), [], [], Es, old_effects
        if t in self.init_program_trans:
            print()
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

        smt_checker = SMTChecker()

        invars = []
        constants = []
        new_effects = {x: y for x, y in old_effects.items()}
        # if the predicate is a state predicate and is not mentioned in both the guard and action
        if not is_tran_pred(predicate) and not any(
                True for v in predicate.variablesin() if v in t.condition.variablesin()
                                                         or v in vars_modified_in_action_without_identity +
                                                         vars_used_in_action_without_identity):
            invars = [predicate]
        # if the predicate is a transition predicate and is not mentioned in the action
        elif is_tran_pred(predicate) and not any(
                True for v in predicate.variablesin() if v in vars_modified_in_action_without_identity):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table, smt_checker):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table,
                              smt_checker):
            constants = [(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]),
                              self.program.symbol_table, smt_checker) and \
                is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]),
                                 self.program.symbol_table, smt_checker):
            # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
            invars = [(predicate)]

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
                if sat(formula_pos, self.program.symbol_table, smt_checker):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = add_prev_suffix(conjunct(guard_disjunct, neg(predicate)))
                if sat(formula_neg, self.program.symbol_table, smt_checker):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()
                if E not in old_effects.keys():
                    print()
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
                                           self.program.symbol_table, smt_checker):
                            new_pos_Ps.add(Ps | {predicate})

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table, smt_checker):
                            new_neg_Ps.add(Ps | {neg(predicate)})
                    self.all_pred_states.add(frozenset(new_pos_Ps))
                    self.all_pred_states.add(frozenset(new_neg_Ps))
                    if len(new_pos_Ps) == 0 and len(new_neg_Ps) == 0:
                        print()
                    new_now = frozenset(P for P in new_neg_Ps | new_pos_Ps)
                    if len(new_now) > 0:
                        newNextPss.put(nextPs, new_now)

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    new_effects.pop(E)
                    Es.remove((guard_disjunct, E))
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            prev_predicate = add_prev_suffix(predicate)
            for (guard_disjunct, E) in Es:
                # E_formula = add_prev_suffix(conjunct_formula_set(E))
                new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))
                formula_pos = conjunct(new_formula, prev_predicate)
                if sat(formula_pos, self.program.symbol_table, smt_checker):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = conjunct(new_formula, neg(prev_predicate))
                if sat(formula_neg, self.program.symbol_table, smt_checker):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()
                if E not in old_effects.keys():
                    print()
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
                                           self.program.symbol_table, smt_checker):
                            new_pos_Ps.add(Ps | {predicate})

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table, smt_checker):
                            new_pos_Ps.add(Ps | {neg(predicate)})

                        # if p was true before, is not p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table, smt_checker):
                            new_neg_Ps.add(Ps | {predicate})

                        # if p was false before, is not p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table, smt_checker):
                            new_neg_Ps.add(Ps | {neg(predicate)})
                    if len(new_pos_Ps) == 0 and len(new_neg_Ps) == 0:
                        print()
                    if len(new_pos_Ps) > 0:
                        newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                    if len(new_neg_Ps) > 0:
                        newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    new_effects.pop(E)
                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def add_transition_predicate_to_t(self, t: Transition, Es, old_effects, predicate):
        if len(old_effects) == 0:
            return t, transition_formula(t), [], [], Es, old_effects

        if not any(True for v in predicate.variablesin() if str(v).endswith("_prev")):
            raise Exception(str(predicate) + " is not a transition predicate.")

        action = t.action
        vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]

        t_formula = transition_formula(t)

        smt_checker = SMTChecker()

        invars = []
        constants = []
        new_effects = {x: y for x, y in old_effects.items()}
        # if the transition predicate is not mentioned in the action
        if not any(True for v in predicate.variablesin() if v in vars_modified_in_action_without_identity):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table, smt_checker):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table,
                              smt_checker):
            constants = [(predicate)]
        # if cannot determine exactly whether to the pred is a constant, then for replicate each post state
        # for each possibility
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            prev_predicate = add_prev_suffix(predicate)
            for (guard_disjunct, E) in Es:
                # E_formula = add_prev_suffix(conjunct_formula_set(E))
                new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))

                newNextPss = InvertibleMap()
                if E not in old_effects.keys():
                    print()
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
                               self.program.symbol_table, smt_checker):
                            new_pos_Ps.add(Ps)

                        if sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                        conjunct(new_formula,
                                                 conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                               self.program.symbol_table, smt_checker):
                            new_pos_Ps.add(Ps)

                    if len(new_pos_Ps) == 0 and len(new_neg_Ps) == 0:
                        print()
                    if len(new_pos_Ps) > 0:
                        newNextPss.put(nextPs_with_p, frozenset(P for P in new_pos_Ps))
                    if len(new_neg_Ps) > 0:
                        newNextPss.put(nextPs_with_neg_p, frozenset(P for P in new_neg_Ps))

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    new_effects.pop(E)
                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def pretty_print_abstract_effect(self):
        for t in self.abstract_effect.keys():
            print(str(t))
            for E in self.abstract_effect[t].keys():
                if len(E) == 0:
                    print("\tevents: ", "true")
                else:
                    print("\tevents: ", ", ".join(str(e) for e in E))
                for nextPs in self.abstract_effect[t][E].keys():
                    print("\t\t", "true" if len(nextPs) == 0 else " and ".join(str(p) for p in nextPs))
                    print("\t\t", " or \n\t\t\t".join(
                        "true" if len(nowPs) == 0 else "(" + " and ".join(str(p) for p in nowPs) + ")" for nowPs in
                        self.abstract_effect[t][E][nextPs]))

    def add_predicates(self,
                       new_interpolants: [Formula],
                       new_ranking_and_invars: dict[Formula, [Formula]],
                       parallelise=True):
        self.interpolants.update(new_interpolants)
        all_new_state_preds = (new_interpolants +
                               list(itertools.chain.from_iterable(new_ranking_and_invars.values())))
        self.add_state_predicates(all_new_state_preds, parallelise)

        self.ranking_and_invars.update(new_ranking_and_invars)
        new_tran_preds = []
        for ranking in new_ranking_and_invars.keys():
            dec = BiOp(add_prev_suffix(ranking), ">", ranking)
            inc = BiOp(add_prev_suffix(ranking), "<", ranking)
            new_tran_preds.append(dec)
            new_tran_preds.append(inc)

        self.add_transition_predicates(new_tran_preds, True)

    def add_state_predicates(self, new_state_predicates: [Formula], parallelise=True):
        if len(new_state_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()
        self.all_pred_states = set()
        for p in new_state_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_state_predicates)):
                    TypedValuation(str(label_pred(p, new_state_predicates)), "bool", true())})

            if parallelise:
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p
                results_env = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.compute_abstract_effect_with_p)(t, self.abstract_guard_env_disjuncts[t],
                                                                 self.abstract_effect[t], p)
                    for t in self.abstract_guard_env.keys() if t not in self.init_program_trans)
                results_con = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.compute_abstract_effect_with_p)(t, self.abstract_guard_con_disjuncts[t],
                                                                 self.abstract_effect[t], p) for t in
                    self.abstract_guard_con.keys())
            else:
                results_env = []
                for t in self.abstract_guard_env.keys():
                    results_env.append(self.compute_abstract_effect_with_p(t, self.abstract_guard_env_disjuncts[t],
                                                                           self.abstract_effect[t], p))

                results_con = []
                for t in self.abstract_guard_con.keys():
                    results_con.append(self.compute_abstract_effect_with_p(t, self.abstract_guard_con_disjuncts[t],
                                                                           self.abstract_effect[t], p))

            # TODO can optimise, since same t may be both env or con
            for t, t_formula, invars, constants, Es, new_effects in results_env:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_constant[t] += constants
                self.abstract_guard_env_disjuncts[t] = Es
                self.abstract_effect[t] = new_effects

            for t, t_formula, invars, constants, Es, new_effects in results_con:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_constant[t] += constants
                self.abstract_guard_con_disjuncts[t] = Es
                self.abstract_effect[t] = new_effects

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
        self.all_pred_states = set()
        for p in new_transition_predicates:
            self.symbol_table.update({
                str(label_pred(p, new_transition_predicates)):
                    TypedValuation(str(label_pred(p, new_transition_predicates)), "bool", true())})

            if parallelise:
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p
                results_env = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.add_transition_predicate_to_t)(t, self.abstract_guard_env_disjuncts[t],
                                                                self.abstract_effect[t], p) for t in
                    self.abstract_guard_env.keys())
                results_con = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.add_transition_predicate_to_t)(t, self.abstract_guard_con_disjuncts[t],
                                                                self.abstract_effect[t], p) for t in
                    self.abstract_guard_con.keys())
            else:
                results_env = []
                for t in self.abstract_guard_env.keys():
                    results_env.append(self.add_transition_predicate_to_t(t, self.abstract_guard_env_disjuncts[t],
                                                                          self.abstract_effect[t], p))

                results_con = []
                for t in self.abstract_guard_con.keys():
                    results_con.append(self.add_transition_predicate_to_t(t, self.abstract_guard_con_disjuncts[t],
                                                                          self.abstract_effect[t], p))

            # TODO can optimise, since same t may be both env or con
            for t, t_formula, invars, constants, Es, new_effects in results_env:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_tran_preds_constant[t_formula] += constants
                self.abstract_guard_env_disjuncts[t] = Es
                self.abstract_effect[t] = new_effects

            for t, t_formula, invars, constants, Es, new_effects in results_con:
                self.abstract_effect_invars[t] += invars
                self.abstract_effect_tran_preds_constant[t_formula] += constants
                self.abstract_guard_con_disjuncts[t] = Es
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
        new_env_transitions, env_to_program_transitions = merge_transitions(self.abstraction.env_transitions,
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

    def to_ltl(self,
               original_ltl_problem: LTLSynthesisProblem,
               ltlAbstractionType: LTLAbstractionType) -> tuple[object, ([Formula], [Formula])]:
        ltl_abstractions = {}
        if ltlAbstractionType.base_type == LTLAbstractionBaseType.explicit_automaton and \
                ltlAbstractionType.transition_type == LTLAbstractionTransitionType.combined and \
                ltlAbstractionType.structure_type == LTLAbstractionStructureType.control_and_predicate_state and \
                ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env:
            self.base_abstraction = self.to_automaton_abstraction()
            return self.base_abstraction, abstract_ltl_problem(original_ltl_problem, self, self.base_abstraction)
        if len(ltl_abstractions) != 1:
            raise NotImplementedError("Options for LTL abstraction not implemented: " + str(ltlAbstractionType))

    def get_symbol_table(self):
        return self.symbol_table

    def get_state_predicates(self):
        return self.state_predicates

    def get_transition_predicates(self):
        return self.transition_predicates

    def get_interpolants(self) -> [Formula]:
        return self.interpolants

    def get_ranking_and_invars(self) -> dict[Formula, [Formula]]:
        return self.ranking_and_invars

    def get_program(self):
        return self.program

    def massage_mealy_machine(self,
                              mm: MealyMachine,
                              base_abstraction,
                              ltlAbstractionType: LTLAbstractionType) -> MealyMachine:
        if ltlAbstractionType.base_type == LTLAbstractionBaseType.explicit_automaton and \
                ltlAbstractionType.transition_type == LTLAbstractionTransitionType.combined and \
                ltlAbstractionType.structure_type == LTLAbstractionStructureType.control_and_predicate_state:
            return mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(self,
                                                                                             self.program,
                                                                                             base_abstraction)
        else:
            raise NotImplementedError("Options for LTL abstraction not implemented: " + str(ltlAbstractionType))

    def concretise_counterexample(self, counterexample: [dict]):
        pass