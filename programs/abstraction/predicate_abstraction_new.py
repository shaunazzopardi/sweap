import time
from itertools import chain, combinations
import logging

from programs.abstraction.explicit_abstraction.util.abstract_state import AbstractState

logger = logging.getLogger(__name__)

from pysmt.shortcuts import And, Not, TRUE
from joblib import Parallel, delayed

from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_preds, add_prev_suffix, stutter_transitions, \
    stutter_transition, symbol_table_from_program, transition_formula, stringify_pred, safe_update_set_vals, safe_update_list_vals, fnode_to_formula, stringify_pred_take_out_neg
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X, true, false, disjunct, simplify_formula_without_math, is_tautology, sat, \
    simplify_formula_with_math, \
    is_contradictory
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()


class PredicateAbstraction:
    def __init__(self, program: Program):
        self.transition_state_tags = {}
        self.transition_unaffected_tags = {}
        self.transition_constant_tags = {}
        self.transition_tran_tags = {}
        self.con_tags = {}
        self.pred_transition_invars = {}
        self.formula_to_trans = {}
        self.formula_to_formula_without_identity_actions = {}
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}

        self.program = program

        self.orig_env_transitions, self.orig_con_transitions = self.program.complete_transitions()
        init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        candidate_init_trans = [t.add_condition(init_conf) for t in self.orig_env_transitions if t.src == self.program.initial_state]
        self.init_program_trans = [t for t in candidate_init_trans if sat(transition_formula(t), self.program.symbol_table)]

        self.all_program_trans = self.orig_env_transitions + self.orig_con_transitions + self.init_program_trans

        self.transition_formula_to_trans = {}
        # TODO for stutter transitions we can avoid computing effects
        for t in self.all_program_trans:
            t_f = transition_formula(t)
            if t_f in self.transition_formula_to_trans.keys():
                self.transition_formula_to_trans[t_f].append(t)
            else:
                self.transition_formula_to_trans[t_f] = [t]

        self.abstract_effect_tran_preds_constant = {}
        self.abstract_effect_tran_preds = {}

        self.con_env_transitions = {}

        self.abstract_guard_con = None
        self.abstract_guard_con_disjuncts = None
        self.abstract_guard_env = None
        self.abstract_guard_env_disjuncts = None
        self.state_predicates = []
        self.transition_predicates = []
        self.loops = []

        self.con_to_program_transitions = None
        self.env_to_program_transitions = None

        self.con_program_transitions_to_abstract = None
        self.env_program_transitions_to_abstract = None

        self.state_to_env_transitions = None
        self.state_to_con_transitions = None

        self.abstraction = None
        self.cache = {}
        self.f_cache = {}
        self.loop_counter = 0
        self.loops = []

    def abstract_program_transition_env(self, env_trans : Transition, symbol_table):
        disjuncts, formula = self.abstract_guard(env_trans.condition, self.program.env_events, symbol_table)
        return env_trans, disjuncts, formula

    def abstract_program_transition_con(self, con_trans: Transition, symbol_table):
        disjuncts, formula = self.abstract_guard(con_trans.condition, self.program.con_events, symbol_table)
        return con_trans, disjuncts, formula

    def abstract_program_transitions(self):

        self.abstract_guard_env = {}
        self.abstract_guard_con = {}
        self.abstract_guard_env_disjuncts = {}
        self.abstract_guard_con_disjuncts = {}

        results_env = Parallel(n_jobs=-1, prefer="threads")(delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in self.orig_env_transitions)

        results_init = Parallel(n_jobs=-1, prefer="threads")(delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in self.init_program_trans)
        results_con = Parallel(n_jobs=-1, prefer="threads")(delayed(self.abstract_program_transition_con)(t, self.program.symbol_table) for t in self.orig_con_transitions)

        for t, disjuncts, formula in results_env + results_init:
            self.abstract_guard_env[t] = formula
            self.abstract_guard_env_disjuncts[t] = disjuncts
            empty_effects = InvertibleMap()
            true_set = {frozenset()}
            empty_effects.put(frozenset(), frozenset(true_set))
            if len(disjuncts) == 0:
                print()
            self.abstract_effect[t] = {E: empty_effects for _, E in disjuncts}
            self.abstract_effect_tran_preds[t] = {E: empty_effects for _, E in disjuncts}

        for t, disjuncts, formula in results_con:
            self.abstract_guard_con[t] = formula
            self.abstract_guard_con_disjuncts[t] = disjuncts
            empty_effects = InvertibleMap()
            true_set = {frozenset()}
            empty_effects.put(frozenset(), frozenset(true_set))
            self.abstract_effect[t] = {E: empty_effects for _, E in disjuncts}
            self.abstract_effect_tran_preds[t] = {E: empty_effects for _, E in disjuncts}

    def abstract_guard_explicitly(self, guard, events, symbol_table):
        smt_checker = SMTChecker()

        if not sat(guard, symbol_table, smt_checker):
            raise Exception("Guard is unsatisfiable: " + str(guard))
        vars_in_cond = guard.variablesin()
        events_in_cond = [e for e in vars_in_cond if e in events]
        if len(events_in_cond) == 0:
            return [(guard, frozenset())], true()

        powerset = powerset_complete(events_in_cond)

        int_disjuncts_only_events = []
        for E in powerset:
            try:
                if sat(conjunct_formula_set(E | {guard}), self.program.symbol_table, smt_checker):
                    int_disjuncts_only_events.append(E)
            except Exception as e:
                raise(e)

        # satisfying_behaviour = []
        # for E in int_disjuncts_only_events:
        #     precedent = implies(conjunct_formula_set(E), guard)
        #     antecedent = []
        #     for EE in int_disjuncts_only_events:
        #         if E is not EE:
        #             antecedent.append(implies(conjunct_formula_set(EE), guard))
        #     if not sat(implies(precedent, disjunct_formula_set(antecedent)), (self.program.symbol_table)):
        #         satisfying_behaviour.append(E)
        #     else:
        #         print()
        satisfying_behaviour = int_disjuncts_only_events

        dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
        disjuncts = []
        for E in satisfying_behaviour:
            if not E:
                logger.info("empty E " + str(guard))
            guard_E = guard.replace(lambda x: true() if x in E else false() if neg(x) in E else x)
            try:
                guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
            except Exception as e:
                # TODO what is this exception caused by??
                guard_E_simplified = simplify_formula_with_math(guard_E, symbol_table)
                print(str(e))
            disjuncts.append((guard_E_simplified, E))

        if len(disjuncts) == 0:
            if sat(guard, symbol_table):
                return [(guard, frozenset())], true()
            else:
                return [], false()
        else:
            return disjuncts, dnfed

    def abstract_guard(self, guard: Formula, events, symbol_table, use_set_method=True):
        return self.abstract_guard_explicitly(guard, events, symbol_table)

    def getFromCache(self, f: Formula):
        if f in self.cache.keys():
            return self.cache[f]
        else:
            Ps = set()
            Ps.add(frozenset())
            return Ps

    def getFromFCache(self, con_turn_flag, t, E):
        if (t, E) in self.f_cache.keys():
            return self.f_cache[(con_turn_flag, t, E)]
        else:
            return None

    def meaning_within(self, f: Formula, predicates: [Formula], symbol_table):
        Ps = self.getFromCache(f)
        return meaning_within_incremental(f, Ps, predicates, symbol_table)

    def prune_predicate_sets(self):
        new_abstract_effect = {}

        for t in self.abstract_guard_con.keys():
            # TODO the keys should be transition formulas,
            #   to avoid repeating the same computation for
            #   different transitions with the same formula
            new_abstract_effect[t] = {}
            t_f = transition_formula(t)
            prev_trans = [tt for tt in self.abstract_guard_env.keys() if tt.tgt == t.src]

            prev_pred_states = set()
            for tt in prev_trans:
                tt_f = transition_formula(tt)
                tt_prev_pred_state = set()
                for _, effects in self.abstract_effect[tt].items():
                    effects_tt_prev_pred_states = [Ps for Ps in effects.keys()]
                    if len(self.abstract_effect_constant[tt]) > 0:
                        effects_tt_prev_pred_states = [Ps | {c for c in self.abstract_effect_constant[tt]} for Ps
                                                       in effects_tt_prev_pred_states]
                    if len(self.abstract_effect_invars[tt]) > 0:
                        invar_powersets = powerset_complete(self.abstract_effect_invars[tt])
                        effects_tt_prev_pred_states = [Ps | P for P in invar_powersets for Ps in
                                                       effects_tt_prev_pred_states]
                    tt_prev_pred_state.update(effects_tt_prev_pred_states)
                prev_pred_states.update(tt_prev_pred_state)

            current_pred_states = [Ps for _, effects in self.abstract_effect[t].items() for Pss in effects.values()
                                   for Ps in Pss]

            pruned_current_pred_states = [Ps for Ps in current_pred_states if set(Ps) in prev_pred_states]

            for E, effects in self.abstract_effect[t].items():
                new_abstract_effect[t][E] = InvertibleMap()
                for nextPs in effects.keys():
                    newPss = frozenset(Ps for Ps in effects.get_value(nextPs) if Ps in pruned_current_pred_states)
                    if len(newPss) > 0:
                        new_abstract_effect[t][E].put(nextPs, newPss)
                if len(new_abstract_effect[t][E]) == 0:
                    del new_abstract_effect[t][E]

            if len(new_abstract_effect[t]) == 0:
                raise Exception("No effect left for transition " + str(t))

        transitive_effects = []
        for t in self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                new_abstract_effect[t] = self.abstract_effect[t]
            else:
                new_abstract_effect[t] = {}
                t_f = transition_formula(t)
                prev_trans = [tt for tt in self.abstract_guard_con.keys() if tt.tgt == t.src]
                current_pred_states = [Ps for _, effects in self.abstract_effect[t].items() for Pss in effects.values()
                                       for Ps in Pss]

                pred_set_to_trans = {}

                prev_pred_states = set()
                pruned_current_pred_states = set()
                for tt in prev_trans:
                    tt_f = transition_formula(tt)
                    tt_prev_pred_state = set()
                    # using the previously pruned new abstract effect of controller transitions
                    for EE, effects in new_abstract_effect[tt].items():
                        effects_tt_prev_pred_states = {Ps: guard for Ps, guard in effects.items()}

                        constants = {c for c in self.abstract_effect_constant[tt]}
                        invar_powersets = powerset_complete(self.abstract_effect_invars[tt])

                        for Ps, guard in effects_tt_prev_pred_states.items():
                            if len(current_pred_states) == len(prev_pred_states):
                                break
                            Ps_with_constants = set(Ps).union(constants)
                            for invar in invar_powersets:
                                Ps_with_invar = Ps_with_constants.union(invar)
                                Ps_with_invar_set = frozenset(Ps_with_invar)
                                pred_set_to_trans[Ps_with_invar_set] = []
                                if Ps_with_invar_set in current_pred_states:
                                    pruned_current_pred_states.add(Ps_with_invar_set)
                                    pred_set_to_trans[Ps_with_invar_set].append((tt.src, EE, guard))

                t_formula = transition_formula(t)
                for E, effects in self.abstract_effect[t].items():
                    new_abstract_effect[t][E] = InvertibleMap()
                    for nextPs, now in effects.items():
                        newPss = frozenset(Ps for Ps in effects.get_value(nextPs) if Ps in pruned_current_pred_states)
                        if len(newPss) > 0:
                            new_abstract_effect[t][E].put(nextPs, newPss)
                            possible_nows = [n for n in now if n in effects.values_single()]
                            for n in possible_nows:
                                EE_and_guards = pred_set_to_trans[n]
                                transitive_effects.append((EE_and_guards, E, nextPs, t_formula, t.tgt))
                    if len(new_abstract_effect[t][E]) == 0:
                        del new_abstract_effect[t][E]

        del self.abstract_effect
        self.abstract_effect = new_abstract_effect

        return transitive_effects

    def initialise(self, debug=True):
        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions()

        # Formula -> (P -> [P])
        for t in self.all_program_trans:
            disjuncts = self.abstract_guard_env_disjuncts[t] if t in self.abstract_guard_env_disjuncts.keys() else self.abstract_guard_con_disjuncts[t]

            formula = transition_formula(t)
            self.formula_to_trans[formula] = t
            self.transition_state_tags[formula] = {frozenset({d}): [[]] for d in disjuncts}
            self.transition_tran_tags[formula] = {frozenset({d}): [[]] for d in disjuncts}
            self.transition_unaffected_tags[formula] = set()
            self.transition_constant_tags[formula] = set()
            self.pred_transition_invars[formula] = set()
            self.abstract_effect_invars[t] = []
            self.abstract_effect_constant[t] = []
            self.abstract_effect_tran_preds_constant[formula] = []

        # self.to_explicit_abstraction()

    def to_explicit_abstraction(self):
        # TODO this procedure is encoding every possible abstract transition
        #      but, with invars we are able to encode multiple transitions with one
        #      when the invar predicate is not relevant to the actions

        states = set()
        env_transitions = []
        new_env_to_program_transitions = {}
        # new_program_env_to_abstract_env_transitions = {}
        # new_program_con_to_abstract_con_transitions = {}
        self.state_to_env_transitions = {}
        self.state_to_con_transitions = {}

        init_st = self.program.initial_state
        states.add(init_st)
        for t in self.init_program_trans:
            t_f = transition_formula(t)
            if t not in self.abstract_effect.keys():
                raise Exception("transition is not in abstract effect: " + str(t))
            if len(self.abstract_effect[t]) == 0:
                print("transition has empty abstract effect: " + str(t))
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_without_tran_preds = set()
                    tran_preds = []
                    for p in nextPs:
                        if any(v for v in p.variablesin() if "_prev" in str(v)):
                            tran_preds.append(p)
                        else:
                            nextPs_without_tran_preds.add(p)
                    nextPs_with_constants = set(nextPs_without_tran_preds).union(self.abstract_effect_constant[t])
                    for P in Ps:
                        invars = set()
                        for p in self.abstract_effect_invars[t]:
                            if p in P:
                                invars.add(p)
                            elif neg(p) in P:
                                invars.add(neg(p))
                        tgt = AbstractState(t.tgt, invars.union(nextPs_with_constants))
                        states.add(tgt)
                        abs_trans = Transition(init_st,
                                              conjunct_formula_set(E),
                                              [],
                                              t.output + [stringify_pred_take_out_neg(t) for t in tran_preds + self.abstract_effect_tran_preds_constant[t_f]],
                                              tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                        safe_update_set_vals(self.state_to_env_transitions, init_st, {abs_trans})
                        # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
                        env_transitions.append(abs_trans)

        for t in self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                continue
            t_f = transition_formula(t)
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_without_tran_preds = set()
                    tran_preds = []
                    for p in nextPs:
                        if any(v for v in p.variablesin() if "_prev" in str(v)):
                            tran_preds.append(p)
                        else:
                            nextPs_without_tran_preds.add(p)
                    nextPs_with_constants = set(nextPs_without_tran_preds).union(self.abstract_effect_constant[t])
                    for P in Ps:
                        invars = set()
                        for p in self.abstract_effect_invars[t]:
                            if p in P:
                                invars.add(p)
                            elif neg(p) in P:
                                invars.add(neg(p))
                        tgt = AbstractState(t.tgt, invars.union(nextPs_with_constants))
                        src = AbstractState(t.src, P)
                        states.add(src)
                        states.add(tgt)
                        abs_trans = Transition(src,
                                              conjunct_formula_set(E),
                                              [],
                                              t.output + [stringify_pred_take_out_neg(t) for t in tran_preds + self.abstract_effect_tran_preds_constant[t_f]],
                                              tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                        safe_update_set_vals(self.state_to_env_transitions, src, {abs_trans})
                        # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
                        # env_transitions.append(abs_trans)

        con_transitions = []
        new_con_to_program_transitions = {}
        for t in self.abstract_guard_con.keys():
            t_f = transition_formula(t)
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_without_tran_preds = set()
                    tran_preds = []
                    for p in nextPs:
                        if any(v for v in p.variablesin() if "_prev" in str(v)):
                            tran_preds.append(p)
                        else:
                            nextPs_without_tran_preds.add(p)
                    nextPs_with_constants = set(nextPs_without_tran_preds).union(self.abstract_effect_constant[t])
                    for P in Ps:
                        invars = set()
                        for p in self.abstract_effect_invars[t]:
                            if p in P:
                                invars.add(p)
                            elif neg(p) in P:
                                invars.add(neg(p))
                        tgt = AbstractState(t.tgt, invars.union(nextPs_with_constants))
                        src = AbstractState(t.src, P)
                        states.add(src)
                        states.add(tgt)
                        abs_trans = Transition(src,
                                              conjunct_formula_set(E),
                                              [],
                                              t.output + [stringify_pred_take_out_neg(t) for t in tran_preds + self.abstract_effect_tran_preds_constant[t_f]],
                                              tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_con_to_program_transitions, abs_trans, {t})
                        safe_update_set_vals(self.state_to_con_transitions, src, {abs_trans})
                        # safe_update_set_vals(new_program_con_to_abstract_con_transitions, t, {abs_trans})
                        # con_transitions.append(abs_trans)

        self.env_to_program_transitions = new_env_to_program_transitions
        self.con_to_program_transitions = new_con_to_program_transitions
        env_transitions = new_env_to_program_transitions.keys()
        con_transitions = new_con_to_program_transitions.keys()

        self.state_to_env_transitions = {}
        self.state_to_con_transitions = {}
        for t in env_transitions:
            safe_update_list_vals(self.state_to_env_transitions, t.src, [t])
        for t in con_transitions:
            safe_update_list_vals(self.state_to_con_transitions, t.src, [t])

        for s in states:
            # TODO this is important for some reason
            #      sometimes that are con_transitions that go to an state with no outgoing env transitions (and vice-versa)
            #      this may indicate a bug in the abstraction algorithm,
            if s not in self.state_to_env_transitions.keys():
                self.state_to_env_transitions[s] = []
            if s not in self.state_to_con_transitions.keys():
                self.state_to_con_transitions[s] = []
        # old_tate_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
        # old_state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

        # for t in env_transitions:
        #     if t not in self.env_to_program_transitions.keys():
        #         print()
        # for t in con_transitions:
        #     if t not in self.con_to_program_transitions.keys():
        #         print()

        for t in new_env_to_program_transitions.keys():
            if t.tgt not in self.state_to_con_transitions.keys():
                print()
        for t in new_con_to_program_transitions.keys():
            if t.tgt not in self.state_to_env_transitions.keys():
                print()


        # self.state_to_env_transitions = {}
        # for t in env_transitions:
        #     safe_update_list_vals(self.state_to_env_transitions, t.src, [t])
        # self.state_to_con_transitions = {}
        # for t in con_transitions:
        #     safe_update_list_vals(self.state_to_con_transitions, t.src, [t])

        program = self.program

        # # TODO, after this can reduce abstract_effects
        # keep_env = set()
        # keep_con = set()
        # new_state_to_env = {}
        # new_state_to_con = {}
        #
        # env_done_states = set()
        # con_done_states = set()
        # next_states = {init_st}
        # env_turn = True
        # prog_state_to_preconditions = {s:set() for s in self.program.states}
        # while len(next_states) > 0:
        #     new_next = set()
        #     for st in next_states:
        #         if env_turn:
        #             env_done_states.add(st)
        #             if st not in self.state_to_env_transitions.keys():
        #                 print()
        #             current_trans = self.state_to_env_transitions[st]
        #             new_state_to_env[st] = self.state_to_env_transitions[st]
        #             keep_env.update(current_trans)
        #             if st != init_st:
        #                 prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
        #             for t in current_trans:
        #                 if t.tgt not in con_done_states:
        #                     new_next.add(t.tgt)
        #         else:
        #             prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
        #             con_done_states.add(st)
        #             current_trans = self.state_to_con_transitions[st]
        #             new_state_to_con[st] = self.state_to_con_transitions[st]
        #             keep_con.update(current_trans)
        #             for t in current_trans:
        #                 if t.tgt not in env_done_states:
        #                     new_next.add(t.tgt)
        #     next_states = new_next
        #     env_turn = not env_turn
        #
        # env_transitions = list(keep_env)
        # con_transitions = list(keep_con)
        #
        # all_prog_trans = self.abstract_effect.keys()
        # for t in all_prog_trans:
        #     all_preconditions = prog_state_to_preconditions[t.src]
        #     all_items = set(self.abstract_effect[t].items())
        #     for E, effects in all_items:
        #         effects.keep_only_values(all_preconditions)
        #         if len(effects) == 0:
        #             del self.abstract_effect[t][E]

        # self.state_to_env_transitions = new_state_to_env
        # self.state_to_con_transitions = new_state_to_con
        # self.pretty_print_abstract_effect()

        self.abstraction = Program("pred_abst_" + program.name, states | {init_st},
                                   init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events + [stringify_pred(t) for t in self.transition_predicates],
                                   False, preprocess=False)

        # self.abstraction = self.simplified_transitions_abstraction()

    # structure: G (Ps -> Cs -> Es -> Q ->  Q' -> Ps')
    # in the hope of a reduced explosion,
    # the other abstraction reproduces the powersets of predicates and env + con actions for each transition
    # This seems like a success! it is producing much smaller abstractions for the cinderella example; but not as small as the two-step one (which benefits from invariants; although synthesis wise they both timeout)
    def abstraction_to_ltl_alternate(self, pred_name_dict_with_negs, simplified=True):
        predicates = self.state_predicates + self.transition_predicates

        new_env_transitions = self.abstraction.env_transitions
        env_to_program_transitions = self.env_to_program_transitions
        new_con_transitions = self.abstraction.con_transitions
        con_to_program_transitions = self.con_to_program_transitions

        ltl_to_program_transitions = {}

        init_transitions = [t for t in new_env_transitions if t.src == self.abstraction.initial_state]
        init_cond_formula_sets = []
        ltl_to_program_transitions["init"] = {}
        for t in init_transitions:
            cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                            conjunct_formula_set(
                                sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                            )
            init_cond_formula_sets.append(cond)
            safe_update_set_vals(ltl_to_program_transitions["init"], cond, env_to_program_transitions[t])

        init_cond_formula = disjunct_formula_set(init_cond_formula_sets)

        init_cond = init_cond_formula.to_nuxmv()

        states = [Variable(s.state) for s in self.abstraction.states if s != self.abstraction.initial_state] + \
                 [Variable(self.abstraction.initial_state)]
        states = set(states)

        at_least_and_at_most_one_state = UniOp("G",
                                               conjunct_formula_set(
                                                   [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                         states
                                                                                         if
                                                                                         r != q]))
                                                    for q in states if "loop" not in str(q)])).to_nuxmv()

        not_init_env_transitions = [t for t in new_env_transitions if
                                    t.src != self.abstraction.initial_state]

        not_init_con_transitions = [t for t in new_con_transitions if
                                    t.src != self.abstraction.initial_state]

        matching_pairs = {}

        # for every state that is not the initial state: s
        # for each controller transition from that state: t
        # get the set of all env transitions that can happen immediately after: ets
        # and match s with the pair of condition of t and ets
        #
        # at the end, every state s is associated with a list of conditions
        # and the associated env transitions that can happen after

        preds_now_to_next = {}
        for t in not_init_con_transitions:
            current_pred_state = conjunct_formula_set(label_preds(t.src.predicates, predicates), sort=True)
            if current_pred_state not in preds_now_to_next.keys():
                preds_now_to_next[current_pred_state] = {}

            con_tran_preds = set()
            for o in t.output:
                if 'prev' in str(o):
                    con_tran_preds.add(o)

            if t.src not in preds_now_to_next[current_pred_state].keys():
                preds_now_to_next[current_pred_state][t.src] = {}
            if t.condition not in preds_now_to_next[current_pred_state][t.src].keys():
                preds_now_to_next[current_pred_state][t.src][t.condition] = {}

            ets = {}
            for et in not_init_env_transitions:
                if et.src.is_instance_of(t.tgt) or t.tgt.is_instance_of(et.src):
                    if et.condition not in preds_now_to_next[current_pred_state][t.src][t.condition].keys():
                        preds_now_to_next[current_pred_state][t.src][t.condition][et.condition] = {}

                    et_current_out = set()
                    et_tran_preds = set()
                    for o in et.output:
                        if 'prev' in str(o):
                            et_tran_preds.add(o)
                        else:
                            et_current_out.add(o)
                    bookkept_tran_preds = bookkeep_tran_preds(con_tran_preds, et_tran_preds)

                    next_state = bookkept_tran_preds | label_preds(et.tgt.predicates, predicates)
                    next_state = conjunct_formula_set(next_state, sort=True)
                    next_here = conjunct_formula_set({Variable(et.tgt.state)} | et_current_out)

                    if next_state not in preds_now_to_next[current_pred_state][t.src][t.condition][et.condition].keys():
                        preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state] = []
                    preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state].append((next_here))

        transitions = []
        for Ps, state_dict in preds_now_to_next.items():
            ps_transitions = []
            for q, events_dict in state_dict.items():
                q_trans = []
                for Cs, ets_dict in events_dict.items():
                    con_trans = []
                    for Es in ets_dict.keys():
                        ps_next_trans = []
                        for next_Ps, next_here in ets_dict[Es].items():
                            next = (conjunct(next_Ps, disjunct_formula_set(next_here)))
                            ps_next_trans.append(next)
                        next = disjunct_formula_set(ps_next_trans)
                        now = (Es)
                        con_trans.append(conjunct(now, next))
                    # not sure this will do anything,
                    # already handled with merge transitions
                    next_state = simplify_formula_without_math(disjunct_formula_set(con_trans))
                    next = X(next_state)
                    now = (Cs)
                    q_trans.append(conjunct(now, next))
                next = disjunct_formula_set(q_trans)
                now = Variable(q.state)
                ps_transitions.append(conjunct(now, next))
            next = disjunct_formula_set(ps_transitions)
            now = (Ps)
            transitions.append(G(implies(now, next)))

        return [init_cond, at_least_and_at_most_one_state] + transitions, ltl_to_program_transitions


    def abstraction_to_ltl(self, pred_name_dict_with_negs, simplified=True):
        predicates = self.state_predicates + self.transition_predicates

        # simplify
        # if simplified:
        #     new_env_transitions, env_to_program_transitions = merge_transitions(self.abstraction.env_transitions,
        #                                                                         self.program.symbol_table,
        #                                                                         self.env_to_program_transitions)
        #     new_con_transitions, con_to_program_transitions = merge_transitions(self.abstraction.con_transitions,
        #                                                                         self.program.symbol_table,
        #                                                                         self.con_to_program_transitions)
        # else:
        #     new_env_transitions = self.abstraction.env_transitions
        #     env_to_program_transitions = self.env_to_program_transitions
        #     new_con_transitions = self.abstraction.con_transitions
        #     con_to_program_transitions = self.con_to_program_transitions

        new_env_transitions = self.abstraction.env_transitions
        env_to_program_transitions = self.env_to_program_transitions
        new_con_transitions = self.abstraction.con_transitions
        con_to_program_transitions = self.con_to_program_transitions

        ltl_to_program_transitions = {}

        init_transitions = [t for t in new_env_transitions if t.src == self.abstraction.initial_state]
        init_cond_formula_sets = []
        ltl_to_program_transitions["init"] = {}
        for t in init_transitions:
            cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                            conjunct_formula_set(
                                sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                            )
            init_cond_formula_sets.append(cond)
            safe_update_set_vals(ltl_to_program_transitions["init"], cond, env_to_program_transitions[t])

        init_cond_formula = disjunct_formula_set(init_cond_formula_sets)

        init_cond = init_cond_formula.to_nuxmv()

        states = [Variable(s.state) for s in self.abstraction.states if s != self.abstraction.initial_state] + \
                 [Variable(self.abstraction.initial_state)]
        states = set(states)

        at_least_and_at_most_one_state = UniOp("G",
                                               conjunct_formula_set(
                                                   [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                         states
                                                                                         if
                                                                                         r != q]))
                                                    for q in states if "loop" not in str(q)])).to_nuxmv()

        not_init_env_transitions = [t for t in new_env_transitions if
                                    t.src != self.abstraction.initial_state]

        not_init_con_transitions = [t for t in new_con_transitions if
                                    t.src != self.abstraction.initial_state]

        matching_pairs = {}

        # for every state that is not the initial state: s
        # for each controller transition from that state: t
        # get the set of all env transitions that can happen immediately after: ets
        # and match s with the pair of condition of t and ets
        #
        # at the end, every state s is associated with a list of conditions
        # and the associated env transitions that can happen after
        for s in self.abstraction.states:
            if s is not self.abstraction.initial_state:
                for t in not_init_con_transitions:
                    if t.src == s:
                        ets = []
                        for et in not_init_env_transitions:
                            if et.src == t.tgt:
                                ets.append(et)
                            else:
                                pass
                        if s in matching_pairs.keys():
                            matching_pairs[s] += [(t, ets)]
                        else:
                            matching_pairs[s] = [(t, ets)]
                    else:
                        pass

        remove_loop_stuff = lambda state: state  # re.split("loop", state)[0]
        con_env_transitions = []
        for c_s, cond_ets in matching_pairs.items():
            now_state_preds = [p for p in c_s.predicates if
                               p in (self.state_predicates + [neg(p) for p in self.state_predicates])]
            now = conjunct(Variable(c_s.state),
                           conjunct_formula_set(sorted(label_preds(now_state_preds, predicates),
                                                       key=lambda x: str(x))))
            next = []
            for (ct, ets) in cond_ets:
                cond = ct.condition
                ct_current_out = set()
                ct_next_out = set()
                for o in ct.output:
                    if 'prev' in str(o):
                        ct_next_out.add(o)
                    else:
                        ct_current_out.add(o)
                now_next = []
                for et in ets:
                    et_current_out = set()
                    et_next_out = set()
                    for o in et.output:
                        if 'prev' in str(o):
                            et_next_out.add(o)
                        else:
                            et_current_out.add(o)

                    bookkept_tran_preds = bookkeep_tran_preds(ct_next_out, et_next_out)
                    next_state = bookkept_tran_preds | label_preds(et.tgt.predicates, predicates)

                    next_here = conjunct(conjunct_formula_set({Variable(et.tgt.state), et.condition} | et_current_out),
                                         conjunct_formula_set(sorted(next_state, key=lambda x: str(x)))
                                         )
                    now_next += [X(next_here)]

                    try:
                        if now not in ltl_to_program_transitions.keys():
                            ltl_to_program_transitions[now] = {}
                        safe_update_list_vals(ltl_to_program_transitions[now], (cond, next_here),
                                              [(con_to_program_transitions[ct],
                                                env_to_program_transitions[et])])
                    except Exception as e:
                        print(str(e))
                        raise e
                # If cond (which is the about the current state) is just True (i.e., it s negation is unsat)
                # then just ignore it
                if isinstance(cond, Value) and cond.is_true():
                    next += [disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x)))]
                else:
                    next += [conjunct(cond, disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x))))]

            next = sorted(set(next), key=lambda x: str(x))

            con_env_transitions += [G(implies(now, disjunct_formula_set(next))).to_nuxmv()]

        # TODO this set is only needed when we have transition predicates
        transition_cond = sorted(set(con_env_transitions), key=lambda x: str(x))

        return [init_cond, at_least_and_at_most_one_state] + transition_cond, ltl_to_program_transitions

    def compute_abstract_effect_with_p_better(self, t : Transition, Es, old_effects, predicate):
        # TODO, keep track of powersets over all predicates
        # with each power set, keep track of the effect of each transition on it,
        # and the subset of the source predicates that are invariant under it.
        pass

    def compute_abstract_effect_with_p_new(self, t_f, condition, action, Es, old_effects, predicate):
        is_tran_pred = any(v for v in predicate.variablesin() if str(v).endswith("_prev"))
        if len(old_effects) == 0:
            return t_f, [], [], Es, old_effects, is_tran_pred

        # TODO
        #   1. keep track of powersets of preds that are satisfiable with guard
        #   then consider the effects of the actions on the new predicates
        #   2. in the first step we do some optimisation, by not considering predicates with variables unmentioned in
        #   guard and right-hand side of actions
        #   3. in the second step we do some optimisation, by checking whether the variables in the candidate effect
        #   predicate are modified in the actions or not
        #   4. if a predicate truth in the next step cannot be determined, then do not explode effect set, but keep track
        #   in separate set, and try to determine it s truth when new predicates are added


        # TODO, if no vars modified, then only need need to abstract guards in terms of predicates, then they maintain same value

        vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
        vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in
                                                a.right.variablesin()]

        t_formula = t_f

        invars = []
        constants = []
        new_effects = {x: y for x, y in old_effects.items()}
        new_Es = []

        smt_checker = SMTChecker()
        # if the predicate is a state predicate and is not mentioned in both the guard and action
        if is_tran_pred:
            if not any(v for v in predicate.variablesin() if v in vars_modified_in_action_without_identity):
                constants = [neg(predicate)]
                new_Es, new_effects = Es, old_effects
            elif is_tautology(implies(t_formula, predicate), self.program.symbol_table, smt_checker):
                constants = [(predicate)]
                new_Es, new_effects = Es, old_effects
            elif is_tautology(implies(t_formula, neg(predicate)), self.program.symbol_table, smt_checker):
                constants = [neg(predicate)]
                new_Es, new_effects = Es, old_effects
            else:
                for (guard_disjunct, E) in Es:
                    newNextPss = InvertibleMap()
                    for (nextPs, Pss) in old_effects[E].items():
                        nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                        nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                        newNextPss.put(nextPs_with_p, Pss)
                        newNextPss.put(nextPs_with_neg_p, Pss)
                    if len(newNextPss) > 0:
                        new_effects[E] = newNextPss
                        new_Es.append((guard_disjunct, E))
                    else:
                        new_effects.pop(E)
            return t_formula, invars, constants, new_Es, new_effects, is_tran_pred
        elif not any(v for v in predicate.variablesin() if v in condition.variablesin()
                                                          or v in vars_modified_in_action_without_identity +
                                                             vars_used_in_action_without_identity):
            invars = [predicate]
        elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table, smt_checker):
            constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table, smt_checker):
            constants = [(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]), self.program.symbol_table, smt_checker) and\
                is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]), self.program.symbol_table, smt_checker):
            # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
            invars = [(predicate)]

        # if predicate is constant or invar, then just add to precondition sets
        if len(constants) > 0 or len(invars) > 0:
            # TODO optimisation: if no variable in predicate is mentioned in guard,
            #  then just explode the precondition set without any sat checks
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

                    if len(new_pos_Ps) == 0 and len(new_neg_Ps) == 0:
                        print()
                    new_now = frozenset(P for P in new_neg_Ps | new_pos_Ps)
                    if len(new_now) > 0:
                        newNextPss.put(nextPs, new_now)

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                    new_Es.append((guard_disjunct, E))
                else:
                    new_effects.pop(E)
        # if predicate is not a constant or invar or a transition predicate, then add to both precondition and postcondition sets
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
                    new_Es.append((guard_disjunct, E))
                else:
                    new_effects.pop(E)
            # if len(new_Es) == 0:
            #     raise Exception("No satisfying guard and event left: " + str(predicate) + " " + str(t))
        return t_formula, invars, constants, new_Es, new_effects, is_tran_pred

    def compute_abstract_effect_with_p(self, t : Transition, Es, old_effects, predicate):
        is_tran_pred = lambda q: any(v for v in q.variablesin() if str(v).endswith("_prev"))

        action = t.action
        # TODO, if no vars modified, then only need need to abstract guards in terms of predicates, then they maintain same value

        vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
        vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in a.right.variablesin()]

        t_formula = transition_formula(t)

        invars = []
        constants = []
        new_effects = {x:y for x,y in old_effects.items()}
        # if the predicate is a state predicate and is not mentioned in both the guard and action
        if not is_tran_pred(predicate) and not any(v for v in predicate.variablesin() if v in t.condition.variablesin()
                                                         or v in vars_modified_in_action_without_identity +
                                                                vars_used_in_action_without_identity):
            invars = [predicate]
        # if the predicate is a transition predicate and is not mentioned in the action
        elif is_tran_pred(predicate) and not any(v for v in predicate.variablesin() if v in vars_modified_in_action_without_identity):
            constants = [neg(predicate)]
        # elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table):
        #     constants = [neg(predicate)]
        # elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table):
        #     constants = [(predicate)]
        # elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]), self.program.symbol_table) and\
        #         is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]), self.program.symbol_table):
        #     # TODO This is a bit too much, still need to consider whether predicate is needed to abstract guard
        #     invars = [(predicate)]
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            prev_predicate = add_prev_suffix(predicate)
            for (guard_disjunct, E, _) in Es:
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
                newNextPss = {}
                if E not in old_effects.keys():
                    print()
                for (nextPs, Pss) in old_effects[E].items():
                    nextPs_with_p = frozenset(p for p in nextPs | {predicate})
                    nextPs_with_neg_p = frozenset(p for p in nextPs | {neg(predicate)})
                    new_pos_Ps = []
                    new_neg_Ps = []
                    for Ps in Pss:
                        # if p was true before, is p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                       conjunct(formula_pos, conjunct_formula_set([add_prev_suffix(P) for P in Ps]))), self.program.symbol_table):
                            new_pos_Ps += [Ps + [predicate]]

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                        conjunct(formula_neg, conjunct_formula_set([add_prev_suffix(P) for P in Ps]))), self.program.symbol_table):
                            new_pos_Ps += [Ps + [neg(predicate)]]

                        # if p was true before, is not p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                       conjunct(formula_pos, conjunct_formula_set([add_prev_suffix(P) for P in Ps]))), self.program.symbol_table):
                            new_neg_Ps += [Ps + [(predicate)]]

                        # if p was false before, is not p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                        conjunct(formula_neg, conjunct_formula_set([add_prev_suffix(P) for P in Ps]))), self.program.symbol_table):
                            new_neg_Ps += [Ps + [neg(predicate)]]
                    if len(new_pos_Ps) == 0 and len(new_neg_Ps) == 0:
                        print()
                    if len(new_pos_Ps) > 0:
                        newNextPss[nextPs_with_p] = new_pos_Ps
                    if len(new_neg_Ps) > 0:
                        newNextPss[nextPs_with_neg_p] = new_neg_Ps

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    new_effects.pop(E)
                    Es.remove((guard_disjunct, E))
        return t, t_formula, invars, constants, Es, new_effects

    def add_transition_predicates(self, new_transition_predicates: [Formula], parallelise=True):
        raise NotImplementedError("This method is not implemented yet.")

    # TODO this needs to be optimised
    #   1. instead of trying every powerset of predicates with each transition
    #   compute incrementally (as before) but with the new data structure
    #   can still parallelise at each step
    #  ---
    #   2. use invars to avoid useless smt calls
    #   ; later, when constructing LTL abstraction, which is of the form Ps -> Q -> ...
    #   put some invars on RHS, with the transition,
    #   e.g. P_0, ..., P_{n-1} & (V q_i & X (q'_i & V ((P_n <-> X P_n) & Ps_j) V ((P_k -> X P'_k) & Ps_k))
    def add_predicates(self, new_state_predicates: [Formula], new_transition_predicates: [Formula], parallelise=False):
        if len(new_state_predicates) + len(new_transition_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")
        logger.info("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()

        # TODO remove this iteration, and all together in compute_abstract_effect_with_p_new
        for p in new_state_predicates + new_transition_predicates:
            if parallelise:
                #shouldn't parallelize here, but the loop within compute_abstract_effect_with_p_new
                results = Parallel(n_jobs=-1, prefer="threads")(
                    delayed(self.compute_abstract_effect_with_p_new)(t_f, ts[0].condition, ts[0].action,
                                                                     self.abstract_guard_env_disjuncts[ts[0]]
                                                                     if ts[0] in self.abstract_guard_env_disjuncts.keys() else
                                                                     self.abstract_guard_con_disjuncts[ts[0]],
                                                                     self.abstract_effect[ts[0]], p)
                                                                        for t_f, ts in self.transition_formula_to_trans.items())
                # results_con = Parallel(n_jobs=-1, prefer="threads")(
                #     delayed(self.compute_abstract_effect_with_p_new)(t, self.abstract_guard_con_disjuncts[t], self.abstract_effect[t], p) for t in self.abstract_guard_con.keys())
            else:
                results = []
                for t_f, ts in self.transition_formula_to_trans.items():
                    results.append(self.compute_abstract_effect_with_p_new(t_f, ts[0].condition, ts[0].action,
                                                                           self.abstract_guard_env_disjuncts[ts[0]]
                                                                           if ts[0] in self.abstract_guard_env_disjuncts.keys() else
                                                                           self.abstract_guard_con_disjuncts[ts[0]],
                                                                           self.abstract_effect[ts[0]], p))

                # results_con = []
                # for t in self.abstract_guard_con.keys():
                #     results_con.append(self.compute_abstract_effect_with_p_new(t, self.abstract_guard_con_disjuncts[t], self.abstract_effect[t], p))

            # TODO can optimise, since same t may be both env or con
            for t_formula, invars, constants, Es, new_effects, is_tran_pred in results:
                for t in self.transition_formula_to_trans[t_formula]:
                    self.abstract_effect_invars[t] += invars
                    if not is_tran_pred:
                        self.abstract_effect_constant[t] += constants
                    else:
                        self.abstract_effect_tran_preds_constant[t_formula] += constants
                    if t in self.abstract_guard_env_disjuncts.keys():
                        self.abstract_guard_env_disjuncts[t] = Es
                    else:
                        self.abstract_guard_con_disjuncts[t] = Es
                    self.abstract_effect[t] = new_effects

        end = time.time()
        logger.info(end - start)

        self.state_predicates += new_state_predicates
        self.transition_predicates += new_transition_predicates

        # TODO if just added transition predicate, then can do less work, can just tag transitions in existing
        #      abstraction by new transition predicates
        # self.to_explicit_abstraction()

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
                    print("\t\t", " or \n\t\t\t".join("true" if len(nowPs) == 0 else "(" + " and ".join(str(p) for p in nowPs) + ")" for nowPs in self.abstract_effect[t][E][nextPs]))

    def allowed_in_abstraction(self, path: [Transition]):
        if len(path) == 0:
            return True

        abstract_trans: [[Transition]] = []
        # assuming env-con alternation in path
        current_abstract_states = {self.abstraction.initial_state}
        current_t_index = 0

        env_turn = True

        while True:
            current_t = path[current_t_index]
            if env_turn:
                tentative_abstract_ts = self.abstract_guard_env[current_t]
            else:
                tentative_abstract_ts = self.abstract_guard_con[current_t]
            abstract_ts = [t for t in tentative_abstract_ts if t.src in current_abstract_states]
            if len(abstract_ts) == 0:
                return False, abstract_trans
            else:
                current_abstract_states = {t.tgt for t in abstract_ts}
                abstract_trans += [abstract_ts]
                current_t_index += 1
                if current_t_index == len(path):
                    return True, abstract_trans
                else:
                    env_turn = not env_turn

    def allowed_in_abstraction_with_new_pred(self, path : [Transition], new_predicate):
        if len(path) == 0:
            return True

        abstract_trans : [[Transition]] = []
        # assuming env-con alternation in path
        current_abstract_states = {self.abstraction.initial_state}
        current_t_index = 0

        env_turn = True

        while True:
            current_t = path[current_t_index]
            if env_turn:
                tentative_abstract_ts = self.env_program_transitions_to_abstract[current_t]
            else:
                tentative_abstract_ts = self.con_program_transitions_to_abstract[current_t]
            abstract_ts = [t for t in tentative_abstract_ts if t.src in current_abstract_states]
            if len(abstract_ts) == 0:
                return False, abstract_trans
            else:
                current_abstract_states = {t.tgt for t in abstract_ts}
                abstract_trans += [abstract_ts]
                current_t_index += 1
                if current_t_index == len(path):
                    return True, abstract_trans
                else:
                    env_turn = not env_turn

    def make_explicit_terminating_loop(self, entry_condition, loop_body: [Transition], exit_transs: [Transition],
                                       exit_predicate):
        self.loops += [(entry_condition, loop_body, exit_transs)]
        new_env = []
        new_env += self.program.env_transitions
        new_con = []
        new_con += self.program.con_transitions
        entry_trans = loop_body[0]
        start = 0

        entry_trans_is_con = entry_trans in self.program.con_transitions
        if entry_trans_is_con:
            entry_trans = stutter_transition(self.program, entry_trans.src, True)
        else:
            start = 1

        old_to_new_env_transitions = {t: {t} for t in
                                      self.program.env_transitions + stutter_transitions(self.program, True)}
        old_to_new_con_transitions = {t: {t} for t in
                                      self.program.con_transitions + stutter_transitions(self.program, False)}

        update_from_to = lambda _action, _from, _to: ([v for v in _action if v.left != _from]
                                                      + [BiOp(_from, ":=", disjunct(v.right, _to)) for v in _action if
                                                         v.left == _from]) \
            if any(v for v in _action if v.left == _from) \
            else _action + [BiOp(_from, ":=", _to)]

        entered_loop = Variable("loop" + str(self.loop_counter) + "_1")

        env_turn = entry_trans in old_to_new_env_transitions.keys()

        env_turn = not env_turn

        # TODO: find unique suffix
        step = 1
        i_t = start
        abstract_state_formula = true()
        symbol_table = symbol_table_from_program(self.program)

        loop_seq_vars = {entered_loop}

        for loop_seq_var in loop_seq_vars:
            symbol_table |= {(str(loop_seq_var) + "_" + str(step)): TypedValuation(
                (str(loop_seq_var) + "_" + str(step)), "bool", false())}

        while i_t < len(loop_body):
            if env_turn:
                if loop_body[i_t] not in old_to_new_env_transitions.keys():
                    step_t = stutter_transition(self.program, loop_body[i_t].src, True)
                else:
                    step_t = loop_body[i_t]
                    i_t += 1

                src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
                tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

                loop_seq_vars |= {src_state, tgt_state}

                for loop_seq_var in loop_seq_vars:
                    symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                        (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

                for k, v in symbol_table_from_program(self.program).items():
                    symbol_table |= {
                        (str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                    symbol_table |= {
                        (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

                ts_renamed = set()
                for t in old_to_new_env_transitions[step_t]:
                    t_renamed = Transition(t.src, t.condition,
                                           update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                          false()), t.output,
                                           t.tgt)
                    ts_renamed |= {t_renamed}
                    new_env += [t_renamed]

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                                                 "=", a.right.replace(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                                            for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_exit:
                        old_to_new_env_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(ttt.action, src_state, false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_env_transitions[tt]}

                        alternate_trans_stay = [tt for tt in old_to_new_env_transitions.keys()
                                                if t != tt and tt.src == t.src
                                                and not smt_checker.check(And(*conjunct(
                                neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                abstract_state_formula).to_smt(symbol_table)))]

                        for tt in alternate_trans_stay:
                            old_to_new_env_transitions[tt] = {
                                Transition(ttt.src, ttt.condition,
                                           update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                          false()),
                                           ttt.output, ttt.tgt)
                                for ttt in old_to_new_env_transitions[tt]}
                old_to_new_env_transitions[step_t] = ts_renamed

            elif not env_turn:
                if loop_body[i_t] not in old_to_new_con_transitions.keys():
                    step_t = stutter_transition(self.program, loop_body[i_t].src, False)
                else:
                    step_t = loop_body[i_t]
                    i_t += 1

                src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
                tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

                loop_seq_vars |= {src_state, tgt_state}

                for loop_seq_var in loop_seq_vars:
                    symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                        (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

                for k, v in symbol_table_from_program(self.program).items():
                    symbol_table |= {
                        (str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                    symbol_table |= {
                        (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}

                loop_seq_vars |= {src_state, tgt_state}

                ts_renamed = set()
                for t in old_to_new_con_transitions[step_t]:
                    t_renamed = Transition(t.src, t.condition,
                                           update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                          false()),
                                           t.output, t.tgt)
                    ts_renamed |= {t_renamed}
                    new_con += [t_renamed]

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                                                 "=", a.right.replace(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                                            for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_exit:
                        old_to_new_con_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(ttt.action, src_state, false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_con_transitions[tt]}

                        alternate_trans_stay = [tt for tt in old_to_new_con_transitions.keys()
                                                if t != tt and tt.src == t.src
                                                and not smt_checker.check(And(*conjunct(
                                neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                abstract_state_formula).to_smt(symbol_table)))]

                        for tt in alternate_trans_stay:
                            old_to_new_con_transitions[tt] = {
                                Transition(ttt.src, ttt.condition,
                                           update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                          false()),
                                           ttt.output, ttt.tgt)
                                for ttt in old_to_new_con_transitions[tt]}
                old_to_new_con_transitions[step_t] = ts_renamed

            # loop_states |= {Variable(t.src + "loop" +  str(self.loop_counter) + "_" + str(step)), Variable(t.tgt + "loop" +  str(self.loop_counter) + "_" + str(step + 1))}

            env_turn = not env_turn
            step += 1

        exit_trans_is_con = any(exit_trans
                                for exit_trans in exit_transs
                                if exit_trans not in old_to_new_env_transitions.keys())

        if env_turn and exit_trans_is_con:
            stutter_t = stutter_transition(self.program, exit_transs[0].src, True)

            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
            tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

            loop_seq_vars |= {src_state, tgt_state}

            for loop_seq_var in loop_seq_vars:
                symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                    (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

            for k, v in symbol_table_from_program(self.program).items():
                symbol_table |= {(str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                symbol_table |= {
                    (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

            ts_renamed = set()
            for t in old_to_new_env_transitions[stutter_t]:
                t_renamed = Transition(t.src, t.condition,
                                       update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                      false()),
                                       t.output, t.tgt)
                ts_renamed |= {t_renamed}
                new_env += [t_renamed]

                abstract_state_formula = conjunct(abstract_state_formula,
                                                  t.condition.replace(lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                      abstract_state_formula).to_smt(symbol_table)))]

                for tt in alternate_trans_exit:
                    old_to_new_env_transitions[tt] = {
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt)
                        for ttt in old_to_new_env_transitions[tt]}

                    alternate_trans_stay = [tt for tt in old_to_new_env_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and not smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_stay:
                        old_to_new_env_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                      false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_env_transitions[tt]}
            old_to_new_env_transitions[stutter_t] = ts_renamed

            step += 1
            env_turn = not env_turn
        elif not env_turn and not exit_trans_is_con:
            stutter_t = stutter_transition(self.program, exit_transs[0].src, False)

            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
            tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

            loop_seq_vars |= {src_state, tgt_state}

            for loop_seq_var in loop_seq_vars:
                symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                    (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

            for k, v in symbol_table_from_program(self.program).items():
                symbol_table |= {(str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                symbol_table |= {
                    (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

            ts_renamed = set()
            for t in old_to_new_con_transitions[stutter_t]:
                t_renamed = Transition(t.src, t.condition,
                                       update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                      false()),
                                       t.output, t.tgt)
                ts_renamed |= {t_renamed}
                new_env += [t_renamed]

                abstract_state_formula = conjunct(abstract_state_formula,
                                                  t.condition.replace(lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                      abstract_state_formula).to_smt(symbol_table)))]

                for tt in alternate_trans_exit:
                    old_to_new_con_transitions[tt] = {
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt)
                        for ttt in old_to_new_con_transitions[tt]}

                    alternate_trans_stay = [tt for tt in old_to_new_con_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and not smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_stay:
                        old_to_new_con_transitions[tt] |= {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                      false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_con_transitions[tt]}
            old_to_new_con_transitions[stutter_t] = ts_renamed
            step += 1
            env_turn = not env_turn

        for exit_trans0 in exit_transs:
            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))

            if env_turn:
                # assert exit_trans == entry_trans
                # assert len(exit_transs) == 1

                tgt_state = Variable("loop" + str(self.loop_counter) + "_1")
                loop_seq_vars |= {src_state, tgt_state}

                exit_trans_renamed = set()
                for exit_trans in old_to_new_env_transitions[exit_trans0]:
                    t = Transition(exit_trans.src, exit_trans.condition,
                                   update_from_to(exit_trans.action, src_state, false()),
                                   exit_trans.output, exit_trans.tgt)
                    exit_trans_renamed |= {t}

                    alternate_trans = [tt for tt in old_to_new_env_transitions.keys() if
                                       exit_trans != tt and exit_trans.src == tt.src]

                    for tt in alternate_trans:
                        old_to_new_env_transitions[tt] = \
                            {Transition(ttt.src, ttt.condition,
                                        update_from_to(update_from_to(ttt.action, tgt_state,
                                                                      conjunct(neg(exit_predicate), src_state)),
                                                       src_state, false()),
                                        ttt.output, ttt.tgt) for ttt in old_to_new_env_transitions[tt]}
                old_to_new_env_transitions[exit_trans0] = exit_trans_renamed

            else:
                tgt_state = Variable("loop" + str(self.loop_counter) + "_0")
                loop_seq_vars |= {src_state, tgt_state}

                exit_trans_renamed = set()
                for exit_trans in old_to_new_con_transitions[exit_trans0]:
                    t = Transition(exit_trans.src, exit_trans.condition,
                                   update_from_to(exit_trans.action, src_state, false()),
                                   exit_trans.output, exit_trans.tgt)
                    exit_trans_renamed |= {t}

                    alternate_trans = [tt for tt in old_to_new_con_transitions.keys() if
                                       exit_trans != tt and exit_trans.src == tt.src]

                    for tt in alternate_trans:
                        old_to_new_con_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state,
                                                                     conjunct(neg(exit_predicate), src_state)),
                                                      src_state,
                                                      false()),
                                       ttt.output, ttt.tgt) for ttt in old_to_new_con_transitions[tt]}
                old_to_new_con_transitions[exit_trans0] = exit_trans_renamed

        if not env_turn:
            src_state = Variable("loop" + str(self.loop_counter) + "_0")
            tgt_state = Variable("loop" + str(self.loop_counter) + "_1")

            loop_seq_vars |= {src_state, tgt_state}

            ts = []
            for entry_trans1 in old_to_new_env_transitions[entry_trans]:
                t = Transition(entry_trans1.src, entry_trans1.condition,
                               update_from_to(update_from_to(entry_trans1.action, tgt_state, src_state), src_state,
                                              false()),
                               entry_trans1.output, entry_trans1.tgt)
                ts += [t]

                alternate_trans = [tt for tt in old_to_new_env_transitions.keys() if
                                   t != tt and t.src == tt.src]

                for tt in alternate_trans:
                    old_to_new_env_transitions[tt] = [
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt) for ttt in old_to_new_env_transitions[tt]]

            old_to_new_env_transitions[entry_trans] = set(ts)

        if entry_trans in old_to_new_env_transitions.keys():
            entry_transs = list(old_to_new_env_transitions[entry_trans])[0]
            entry_trans_renamed = Transition(entry_transs.src, entry_transs.condition,
                                             update_from_to(entry_transs.action, entered_loop,
                                                            conjunct(entry_condition,
                                                                     neg(disjunct_formula_set(loop_seq_vars)))),
                                             entry_transs.output, entry_transs.tgt)

            old_to_new_env_transitions[entry_trans] = {entry_trans_renamed}
        else:
            entry_transs = list(old_to_new_con_transitions[entry_trans])[0]
            entry_trans_renamed = Transition(entry_transs.src, entry_transs.condition,
                                             update_from_to(entry_transs.action, entered_loop,
                                                            conjunct(entry_condition,
                                                                     neg(disjunct_formula_set(loop_seq_vars)))),
                                             entry_transs.output, entry_transs.tgt)

            old_to_new_con_transitions[entry_trans] = {entry_trans_renamed}

        new_program = Program(self.program.name, self.program.states,
                              self.program.initial_state,
                              self.program.valuation + [TypedValuation(v.name, "bool", false()) for v in loop_seq_vars],
                              [v for V in old_to_new_env_transitions.values() for v in V],
                              [v for V in old_to_new_con_transitions.values() for v in V],
                              self.program.env_events, self.program.con_events, self.program.out_events)
        self.program = new_program
        print(self.program.to_dot())
        self.loop_counter += 1

        return loop_seq_vars

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


def merge_transitions(transitions: [Transition], symbol_table, to_program_transitions):
    # can probably do this while building the initial abstraction
    new_transitions = []
    new_to_program_transitions = {}

    # partition the transitions into classes where in each class each transition has the same outputs and source and end state
    partitions = dict()
    for transition in transitions:
        key = str(transition.src) + str(conjunct_formula_set(sorted(transition.output, key=lambda x: str(x)))) + str(
            transition.tgt)
        if key in partitions.keys():
            partitions[key].append(transition)
        else:
            partitions[key] = [transition]
    if len(partitions) == len(transitions):
        return transitions, to_program_transitions
    for key in partitions.keys():
        trans_here = partitions[key]
        conditions = disjunct_formula_set(sorted([t.condition for t in trans_here], key=lambda x: str(x)))
        conditions_smt = conditions.to_smt(symbol_table)[0]
        # If negation is unsat
        if not smt_checker.check(Not(conditions_smt)):
            conditions_simplified_fnode = TRUE()
        else:
            conditions_simplified_fnode = conditions_smt#simplify(conditions_smt)#.simplify()
        ## simplify when doing disjunct, after lex ordering
        ## also, may consider when enumerating possible event sets starting with missing some evetns and seeing how many transitions they match, if only then can stop adding to it
        try:
            new_tran = Transition(trans_here[0].src, fnode_to_formula(conditions_simplified_fnode), [],
                                  trans_here[0].output,
                                  trans_here[0].tgt)
            new_transitions.append(new_tran)

            if any(tt for tt in trans_here if tt not in to_program_transitions.keys()):
                raise Exception("Transition not in to program transitions")

            safe_update_set_vals(new_to_program_transitions, new_tran,
                        set(t for tt in trans_here for t in to_program_transitions[tt]))
        except Exception as e:
            raise e
    return new_transitions, new_to_program_transitions


def meaning_within_incremental(f: Formula, previous_preds: [[Formula]], new_preds: [Formula], symbol_table):
    Ps = previous_preds

    for new_pred in new_preds:
        Pss = set()
        for ps in Ps:
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table))):
                Pss.add(frozenset(ps | {new_pred}))

                if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(new_pred)}).to_smt(symbol_table))):
                    Pss.add(frozenset(ps | {neg(new_pred)}))
            else:
                Pss.add(frozenset(ps | {neg(new_pred)}))
        Ps = Pss

    return Ps


def meaning_within_incremental_one_step(f: Formula, previous_preds: [[Formula]], new_pred: Formula, symbol_table):
    Ps = set()

    for ps in previous_preds:
        if smt_checker.check(And(*conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table))):
            Ps.add(ps | {new_pred})
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(new_pred)}).to_smt(symbol_table))):
                Ps.add(ps | {neg(new_pred)})
        else:
            Ps.add(ps | {neg(new_pred)})

    return Ps


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


def powerset(S: set):
    subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))

    return sorted(list(map(set, subsets)), key=lambda x: len(x))


def tran_and_state_preds_after_con_env_step(env_trans: Transition):
    if True:
        src_tran_preds = [p for p in env_trans.src.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]
        tgt_tran_preds = [p for p in env_trans.tgt.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]

        pos = {p for p in (src_tran_preds + tgt_tran_preds) if not isinstance(p, UniOp)}
        all_neg = {p for p in (src_tran_preds + tgt_tran_preds) if isinstance(p, UniOp)}
        neg = {p for p in all_neg if p.right not in pos}

        state_preds = [p for p in env_trans.tgt.predicates
                      if [] == [v for v in p.variablesin() if v.name.endswith("_prev")]]

        return list(pos | neg) + state_preds


def bookkeep_tran_preds(con_tran_preds, env_tran_preds):
    if True:
        pos = {p for p in (con_tran_preds | env_tran_preds) if not isinstance(p, UniOp)}
        all_neg = {p for p in (con_tran_preds | env_tran_preds) if isinstance(p, UniOp)}
        neg = {p for p in all_neg if p.right not in pos}

        return (pos | neg)


class InvertibleMap():

    def __init__(self):
        self.dic = dict()
        self.inv_dic = dict()

    def __getitem__(self, item):
        return self.dic[item]

    def put(self, key, value):
        self.dic[key] = value
        for v in value:
            v_as_key = frozenset(v)
            if v_as_key in self.inv_dic.keys():
                self.inv_dic[v_as_key].append(key)
            else:
                self.inv_dic[v_as_key] = [key]

    def get_value(self, key):
        return self.dic[key]

    def get_key(self, value):
        return self.inv_dic[value]

    def remove_value(self, value):
        relevant_keys = self.inv_dic[value]
        for key in relevant_keys:
            self.dic[key].remove(value)
        del self.inv_dic[value]

    def keep_only_values(self, values):
        relevant_keys = set()
        vals_to_remove = set()
        for v in self.inv_dic.keys():
            if v in values:
                relevant_keys.update(self.inv_dic[v])
            else:
                vals_to_remove.add(v)
        for v in vals_to_remove:
            del self.inv_dic[v]
        for key in relevant_keys:
            # prev = len(self.dic[key])
            new = self.dic[key].intersection(values)
            if len(new) == 0:
                del self.dic[key]
            else:
                self.dic[key] = new

        to_remove_keys = {k for k in self.dic.keys() if k not in relevant_keys}
        for k in to_remove_keys:
            del self.dic[k]
            # now = len(self.dic[key])
            # print("Removed: " + str(prev - now) + " preconditions.")

    def items(self):
        return self.dic.items()

    def keys(self):
        return self.dic.keys()

    def values(self):
        return self.dic.values()

    def values_single(self):
        return self.inv_dic.keys()

    def __len__(self):
        return len(self.dic)

