import time
from itertools import chain, combinations
import logging

from programs.abstraction.explicit_abstraction.util.abstract_state import AbstractState

logger = logging.getLogger(__name__)

from pysmt.shortcuts import And, TRUE, Not
from joblib import Parallel, delayed

from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import add_prev_suffix, stutter_transitions, \
    stutter_transition, symbol_table_from_program, transition_formula, stringify_pred, stringify_formula, \
    safe_update_set_vals
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X, true, false, disjunct, simplify_formula_without_math, is_tautology, sat, \
    keep_only_vars, dnf, partially_evaluate, is_dnf, abstract_out_conjunctions_of_atoms, depth_of_formula, \
    abstract_out_disjunctions_of_atoms, atomic_predicates, F, type_constraints, W, simplify_formula_with_math, \
    is_contradictory, fnode_to_formula
from prop_lang.value import Value
from prop_lang.variable import Variable


class PredicateAbstraction:
    def __init__(self, program: Program):
        self.formula_to_trans = {}
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_relevant_preds = {}
        self.abstract_effect_irrelevant_preds = {}
        self.abstract_effect_tran_preds_constant = {}
        self.all_pred_states = set()

        self.con_env_transitions = {}

        self.init_program_trans = None
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
        self.program = program
        self.cache = {}
        self.f_cache = {}
        self.loop_counter = 0
        self.loops = []

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
            delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in orig_env_transitions + stutter_env)
        init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        self.init_program_trans = [t.add_condition(init_conf) for t in orig_env_transitions + stutter_env if
                                   t.src == self.program.initial_state and sat(conjunct(init_conf, t.condition),
                                                                               self.program.symbol_table)]
        results_init = Parallel(n_jobs=n_jobs, prefer="threads", verbose=11)(
            delayed(self.abstract_program_transition_env)(t, self.program.symbol_table) for t in
            self.init_program_trans)
        results_con = Parallel(n_jobs=n_jobs, prefer="threads", verbose=11)(
            delayed(self.abstract_program_transition_con)(t, self.program.symbol_table) for t in orig_con_transitions + stutter_cons)

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
        if use_set_method:
            return self.abstract_guard_explicitly(guard, events, symbol_table)

        guard_without_math = guard.replace_math_exprs(0)
        # when there is a disjunction, instead of resolving vars to false, resolve them to a var 'program_choice'
        # then, if there is a disjunct with just program_choice in it, it denotes the transition may be activated
        # regardless of what the env does with env vars
        guard_with_only_events0 = keep_only_vars(guard_without_math[0], events,
                                                 make_program_choices_explicit=True).simplify()
        guard_with_only_events = simplify_formula_without_math(guard_with_only_events0)
        abstract_out_disjunctions = abstract_out_disjunctions_of_atoms(guard_with_only_events)
        new_abstract_out_disjunctions = {}
        for var, disjunct in abstract_out_disjunctions[1].items():
            if isinstance(disjunct, BiOp) and disjunct.op[0] == "|":
                disjuncts = set(disjunct.sub_formulas_up_to_associativity())
                if Variable("program_choice") in disjuncts:
                    disjuncts.remove(Variable("program_choice"))
                    disjuncts.add(conjunct_formula_set([neg(d) for d in disjuncts]))
                new_abstract_out_disjunctions[var] = disjunct_formula_set(disjuncts)
            else:
                if not disjunct == Variable("program_choice"):
                    new_abstract_out_disjunctions[var] = disjunct

        guard_with_only_events = abstract_out_disjunctions[0].replace_vars(
            lambda x: x if str(x) not in new_abstract_out_disjunctions.keys()
            else new_abstract_out_disjunctions[str(x)])
        guard_with_only_events = guard_with_only_events.replace_vars(
            BiOp(Variable("program_choice"), ":=", Value("TRUE")))
        # TODO need to timeout and give up on this dnfing sometimes too
        # dnf_guard_with_only_events = dnf(guard_with_only_events, simplify=False)
        val = dnf(guard_with_only_events)

        if val is None:
            print("Giving up on dnfing, and using explicit method.")
            use_set_method = True
            vars_in_cond = guard.variablesin()
            events_in_cond = [e for e in vars_in_cond if e in events]
            powerset = powerset_complete(events_in_cond)

            smt_checker = SMTChecker()
            int_disjuncts_only_events = [E for E in powerset if
                                         smt_checker.check(
                                             And(*conjunct_formula_set(E | {guard}).to_smt(self.program.symbol_table)))]

        else:
            dnf_guard_with_only_events = val

            if Variable("program_choice") in dnf_guard_with_only_events.variablesin():
                print()
            int_disjuncts_only_events = set()
            if isinstance(dnf_guard_with_only_events, BiOp) and dnf_guard_with_only_events.op[0] == "|":
                for d in dnf_guard_with_only_events.sub_formulas_up_to_associativity():
                    if isinstance(d, BiOp) and d.op[0] == "&":
                        atoms = d.sub_formulas_up_to_associativity()
                        contradictions = [a for a in d.variablesin() if a in atoms and neg(a) in atoms]
                        basic_atoms = [a for a in atoms if isinstance(a, Variable) and a not in contradictions
                                       or isinstance(a, UniOp) and a.right not in contradictions]
                        new_conjuncts = [basic_atoms]
                        while len(contradictions) > 0:
                            next_conjuncts = []
                            for at in new_conjuncts:
                                next_conjuncts.append(at + [contradictions[0]])
                                next_conjuncts.append(at + [neg(contradictions[0])])
                            contradictions.pop(0)
                            new_conjuncts = next_conjuncts
                        unique_new_conjuncts = frozenset({frozenset(dd) for dd in new_conjuncts})
                        for dd in unique_new_conjuncts:
                            int_disjuncts_only_events.add(dd)
                    else:
                        int_disjuncts_only_events.add(frozenset({d}))
            else:
                if isinstance(dnf_guard_with_only_events, BiOp) and dnf_guard_with_only_events.op[0] == "&":
                    atoms = dnf_guard_with_only_events.sub_formulas_up_to_associativity()
                    contradictions = [a for a in dnf_guard_with_only_events.variablesin() if
                                      a in atoms and neg(a) in atoms]
                    basic_atoms = [a for a in atoms if isinstance(a, Variable) and a not in contradictions
                                   or isinstance(a, UniOp) and a.right not in contradictions]
                    new_conjuncts = [basic_atoms]
                    while len(contradictions) > 0:
                        next_conjuncts = set(new_conjuncts)
                        for at in new_conjuncts:
                            next_conjuncts.add(at + [contradictions[0]])
                            next_conjuncts.add(at + [neg(contradictions[0])])
                        contradictions.pop(0)
                        new_conjuncts = next_conjuncts
                    unique_new_conjuncts = frozenset({frozenset(dd) for dd in new_conjuncts})
                    for dd in unique_new_conjuncts:
                        int_disjuncts_only_events.add(dd)
                else:
                    int_disjuncts_only_events.add(frozenset({dnf_guard_with_only_events}))

            if len(int_disjuncts_only_events) > 1 and frozenset({Value("TRUE")}) in int_disjuncts_only_events:
                int_disjuncts_only_events.remove(frozenset({Value("TRUE")}))
            event_guard = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
            if not is_tautology(implies(guard, event_guard), self.program.symbol_table):
                disjuncts_to_add = set()
                for d in int_disjuncts_only_events:
                    for dd in d:
                        disjuncts_to_add |= {frozenset({neg(dd).simplify()})}
                for d in disjuncts_to_add:
                    int_disjuncts_only_events.add(d)

            put_math_back = lambda f, d: f.replace_vars(lambda v: d[str(v)] if str(v) in d.keys() else v)

            int_disjuncts = set()
            for d in int_disjuncts_only_events:
                new_guard = partially_evaluate(guard, [v for v in d if isinstance(v, Variable)],
                                               [v.right for v in d if isinstance(v, UniOp) and v.op[0] == "!"] +
                                               [e for e in events if e not in d and neg(e) not in d],
                                               self.program.symbol_table)
                if isinstance(new_guard, Value) and new_guard.is_false():
                    continue
                d_and_guard_without_atomic_conjunctions, conj_dict = abstract_out_conjunctions_of_atoms(new_guard, {})
                d_and_guard_without_math = d_and_guard_without_atomic_conjunctions.replace_math_exprs(0)
                d_and_guard = d_and_guard_without_math[0]
                # dnf is exponential, so if more than 8 variables we give up and just compute all possible combinations of events
                # TODO consider also a timeout, and/or anlayse if d_and_guard is already in dnf form
                # TODO this will mostly happen for the implicit stutter transitions,
                #  so if we leave them for last, we can collect all the info from the smaller transitions
                if is_dnf(d_and_guard):
                    dnf_d_and_guard = d_and_guard
                else:
                    if len(d_and_guard.variablesin()) > 8 and depth_of_formula(d_and_guard) > 3:
                        print("Giving up on dnfing, and using explicit method.")
                        use_set_method = True
                        break
                    val = dnf(d_and_guard)

                    if val is None:
                        print("Giving up on dnfing, and using explicit method.")
                        use_set_method = True
                        break
                    else:
                        dnf_d_and_guard = val

                new_d = d
                if isinstance(dnf_d_and_guard, BiOp) and dnf_d_and_guard.op[0] == "|":
                    collect_disjuncts = set()
                    for dd in dnf_d_and_guard.sub_formulas_up_to_associativity():
                        dd_with_math = put_math_back(dd, conj_dict | d_and_guard_without_math[1])
                        if sat(conjunct(guard, dd_with_math), self.program.symbol_table):
                            collect_disjuncts.add(dd_with_math)
                    if len(collect_disjuncts) > 0:
                        int_disjuncts.add((disjunct_formula_set(collect_disjuncts), new_d))
                else:
                    d_with_math = put_math_back(dnf_d_and_guard, conj_dict | d_and_guard_without_math[1])
                    if sat(conjunct(guard, d_with_math), self.program.symbol_table):
                        int_disjuncts.add((d_with_math, new_d))

        if not use_set_method:
            dnfed = disjunct_formula_set([conjunct_formula_set(d) for _, d in int_disjuncts])
            print(str(guard) + " -> " + str(dnfed))
            return int_disjuncts, dnfed
        else:
            satisfying_behaviour = int_disjuncts_only_events
            dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
            print(str(guard) + " -> " + str(dnfed))

            return [(conjunct(guard, conjunct_formula_set(E)), E) for E in satisfying_behaviour], dnfed

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

    def prune_based_on_explicit_abstraction(self):
        states = set()
        env_transitions = []
        new_env_to_program_transitions = {}
        # new_program_env_to_abstract_env_transitions = {}
        # new_program_con_to_abstract_con_transitions = {}

        init_st = self.program.initial_state
        states.add(init_st)
        for t in self.init_program_trans:
            t_f = transition_formula(t)
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_with_constants = set(nextPs).union(self.abstract_effect_constant[t])
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
                                               t.output,
                                               tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                        # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
                        env_transitions.append(abs_trans)

        for t in self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                continue
            t_f = transition_formula(t)
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_with_constants = set(nextPs).union(self.abstract_effect_constant[t])
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
                                               t.output,
                                               tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                        # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
                        env_transitions.append(abs_trans)

        con_transitions = []
        new_con_to_program_transitions = {}
        for t in self.abstract_guard_con.keys():
            t_f = transition_formula(t)
            for E, effects in self.abstract_effect[t].items():
                for nextPs, Ps in effects.items():
                    nextPs_with_constants = set(nextPs).union(self.abstract_effect_constant[t])
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
                                               t.output,
                                               tgt).complete_outputs(self.program.out_events)
                        safe_update_set_vals(new_con_to_program_transitions, abs_trans, {t})
                        # safe_update_set_vals(new_program_con_to_abstract_con_transitions, t, {abs_trans})
                        con_transitions.append(abs_trans)

        self.env_to_program_transitions = new_env_to_program_transitions
        self.con_to_program_transitions = new_con_to_program_transitions

        for t in env_transitions:
            if t not in self.env_to_program_transitions.keys():
                print()
        for t in con_transitions:
            if t not in self.con_to_program_transitions.keys():
                print()

        self.state_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
        self.state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

        self.env_to_program_transitions = new_env_to_program_transitions
        self.con_to_program_transitions = new_con_to_program_transitions

        program = self.program

        # TODO, after this can reduce abstract_effects
        keep_env = set()
        keep_con = set()
        new_state_to_env = {}
        new_state_to_con = {}

        env_done_states = set()
        con_done_states = set()
        next_states = {init_st}
        env_turn = True
        prog_state_to_preconditions = {s: set() for s in self.program.states}
        while len(next_states) > 0:
            new_next = set()
            for st in next_states:
                if env_turn:
                    env_done_states.add(st)
                    current_trans = self.state_to_env_transitions[st]
                    new_state_to_env[st] = self.state_to_env_transitions[st]
                    keep_env.update(current_trans)
                    if st != init_st:
                        prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
                    for t in current_trans:
                        if t.tgt not in con_done_states:
                            new_next.add(t.tgt)
                else:
                    prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
                    con_done_states.add(st)
                    current_trans = self.state_to_con_transitions[st]
                    new_state_to_con[st] = self.state_to_con_transitions[st]
                    keep_con.update(current_trans)
                    for t in current_trans:
                        if t.tgt not in env_done_states:
                            new_next.add(t.tgt)
            next_states = new_next
            env_turn = not env_turn

        env_transitions = list(keep_env)
        con_transitions = list(keep_con)

        all_prog_trans = self.abstract_effect.keys()
        for t in all_prog_trans:
            all_preconditions = prog_state_to_preconditions[t.src]
            all_items = self.abstract_effect[t].items()
            to_remove = []
            for E, effects in all_items:
                effects.keep_only_values(all_preconditions)
                if len(effects) == 0:
                    to_remove.append(E)
            for E in to_remove:
                del self.abstract_effect[t][E]

        # self.state_to_env_transitions = new_state_to_env
        # self.state_to_con_transitions = new_state_to_con

        self.abstraction = Program("pred_abst_" + program.name, states | {init_st},
                                   init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events, False)

    def prune_predicate_sets(self):
        new_abstract_effect = {}

        for t in self.abstract_guard_con.keys():
            new_abstract_effect[t] = {}
            t_f = transition_formula(t)
            prev_trans = [tt for tt in self.abstract_guard_env.keys() if tt.tgt == t.src]

            prev_pred_states = set()
            for tt in prev_trans:
                tt_f = transition_formula(tt)
                tt_prev_pred_state = set()
                for _, effects in self.abstract_effect[tt].items():
                    effects_tt_prev_pred_states = [Ps for Ps in effects.keys()]
                    if len(self.abstract_effect_constant[t]) > 0:
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

        for t in self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                new_abstract_effect[t] = self.abstract_effect[t]
            else:
                new_abstract_effect[t] = {}
                t_f = transition_formula(t)
                prev_trans = [tt for tt in self.abstract_guard_con.keys() if tt.tgt == t.src]
                current_pred_states = set()
                effect_of_pred_state = {}
                for E, effects in self.abstract_effect[t].items():
                    effect_of_pred_state_with_E = {}
                    for nextPss, Pss in effects.items():
                        for Ps in Pss:
                            current_pred_states.add(Ps)
                            if Ps in effect_of_pred_state_with_E.keys():
                                effect_of_pred_state_with_E[Ps].add(nextPss)
                            else:
                                effect_of_pred_state_with_E[Ps] = {nextPss}
                    effect_of_pred_state.update(effect_of_pred_state_with_E)

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
                                if Ps_with_invar in current_pred_states:
                                    pruned_current_pred_states.add(Ps_with_invar_set)
                                    pred_set_to_trans[Ps_with_invar_set].append((tt.src, EE, guard))

                transitive_effects = []
                for E, effects in self.abstract_effect[t].items():
                    new_abstract_effect[t][E] = InvertibleMap()
                    for nextPs in effects.keys():
                        newPss = frozenset(Ps for Ps in effects.get_value(nextPs) if Ps in pruned_current_pred_states)
                        if len(newPss) > 0:
                            new_abstract_effect[t][E].put(nextPs, newPss)
                            if nextPs in pred_set_to_trans.keys():
                                EE_and_guards = pred_set_to_trans[nextPs]
                                transitive_effects.append((EE_and_guards, E, nextPs, t.tgt))
                    if len(new_abstract_effect[t][E]) == 0:
                        del new_abstract_effect[t][E]

        del self.abstract_effect
        self.abstract_effect = new_abstract_effect

    def loop_abstraction(self,
                         entry_condition,
                         loop_body,
                         exit_predicate_state: Formula,
                         ranking_function: MathExpr,
                         invars: Formula,
                         disagreed_on_program_state: dict,
                         program_taken_transition: Transition):
        # ASSUMPTION: the loop body has been pre-processes to keep only actions that affect the ranking function
        # as in synthesis.liveness_step
        #
        # if there are only decreases of the ranking function in the loop body, then just GF rf_dec -> GF rf_inc is enough
        # if there are also increases, then need to specialise to the actions that affect the rf in the loop body

        new_env_variables = []
        new_con_variables = []
        new_state_predicates = []
        new_transition_predicates = []
        new_guarantees = []
        new_assumptions = []

        # first check who wanted to remain in the loop
        # last_mm_state = [st for st in disagreed_on_program_state.keys() if st.startswith("st_") and "seen" not in st and disagreed_on_program_state[st] == "TRUE"][0]
        env_wanted_to_remain_in_loop = program_taken_transition[0] != loop_body[0][
            0]  # any(True for _, dict in loop_body if dict[last_mm_state] == "TRUE")

        # # check if the actual predicate state of the program appears already in the loop body (counterexample_loop)
        # actual_program_true_preds = [p for p in disagreed_on_program_state.keys() if
        #                              str(p).startswith("pred_") and disagreed_on_program_state[p] == "TRUE"]
        # actual_program_false_preds = [neg(p) for p in disagreed_on_program_state.keys() if
        #                               str(p).startswith("pred_") and disagreed_on_program_state[p] == "FALSE"]
        # actual_program_predicate_state = conjunct_formula_set(
        #     actual_program_true_preds + actual_program_false_preds, sort=True)
        #
        # for _, dict in loop_body:
        #     true_preds = [p for p in dict.keys() if
        #                   str(p).startswith("pred_") and dict[p] == "TRUE"]
        #     false_preds = [neg(p) for p in dict.keys() if
        #                    str(p).startswith("pred_") and dict[p] == "FALSE"]
        #     predicate_state = conjunct_formula_set(true_preds + false_preds, sort=True)
        #     if predicate_state == actual_program_predicate_state:
        #         env_wanted_to_remain_in_loop = False
        #         break

        rf_dec = BiOp(add_prev_suffix(ranking_function), ">", ranking_function)
        rf_inc = BiOp(add_prev_suffix(ranking_function), "<", ranking_function)
        rf_stutter = BiOp(ranking_function, "=", add_prev_suffix(ranking_function))

        # entry_condition can be of three types:
        # (1) true
        # (2) a conjunction of known state predicates
        # (3) a valuation,
        # TODO in the latter two cases we will want to try and expand the entry_condition
        # for now, we add predicates in the entry_condition that are not already present as new state predicates
        entry_predicates = atomic_predicates(entry_condition)
        entry_predicates = [p for p in entry_predicates if not (isinstance(p, Value) and (p.is_true() or p.is_false()))]
        # TODO check if can be expressed with current predicates, with meaning_within
        # entry_predicates = reduce_up_to_iff(entry_predicates, self.state_predicates, self.program.symbol_table)

        # now computing the transition predicates
        # check whether given the loop invariants, and the type constrains of the variables,
        # an action is associated with an increase or decrease or it could be either

        only_dec = False
        action_sequence = []
        for t, _ in loop_body:
            actions = []
            for act in t.action:
                if act.left != act.right:
                    action_formula = BiOp(act.left, "=", add_prev_suffix(act.right))
                    type_constraint = type_constraints(action_formula, self.program.symbol_table)

                    if sat(conjunct_formula_set(
                            [rf_dec, type_constraint, action_formula, invars, add_prev_suffix(invars)]),
                           self.program.symbol_table):
                        if not sat(conjunct_formula_set(
                                [rf_inc, type_constraint, action_formula, invars, add_prev_suffix(invars)]),
                                   self.program.symbol_table):
                            only_dec = True

                    actions.append(action_formula)
            if len(actions) > 0:
                action_sequence.append(conjunct_formula_set(actions, sort=True))
        if only_dec and env_wanted_to_remain_in_loop:
            new_assumptions += [implies(G(F(conjunct(stringify_pred(rf_dec), invars))),
                                        G(F(disjunct(stringify_pred(rf_inc), neg(invars)))))]
            new_transition_predicates += [rf_dec, rf_inc]
        else:
            new_state_predicates += list(entry_predicates) + list(set(action_sequence))
            new_transition_predicates += action_sequence + [rf_stutter]
            action_sequence = [stringify_pred(p) for p in action_sequence]

            in_loop = Variable("inloop_" + str(len(self.loops)))
            loop_index = len(self.loops)

            new_env_variables += [in_loop]
            # building abstract loop constraints
            safety = []
            # initially not in loop
            safety.append(neg(in_loop))

            # entry into abstract loop
            if str(entry_condition).lower() == "true":
                entering_loop = conjunct(neg(in_loop), X(action_sequence[0]))
            else:
                entering_loop = conjunct(neg(in_loop), entry_condition)
                not_entering_loop = conjunct(neg(in_loop), neg(entry_condition))

                safety.append(G(implies(not_entering_loop, X(neg(in_loop)))))

            if len(action_sequence) > 1:
                steps = []
                for i in range(len(action_sequence[1:])):
                    steps.append(Variable("step_" + str(loop_index) + "_" + str(i + 1)))

                new_env_variables += steps

                safety.append(conjunct_formula_set(neg(s) for s in steps))
                # being in one step implies not being in the other steps
                safety.append(conjunct_formula_set(
                    [G(implies(s, neg(disjunct_formula_set([not_s for not_s in steps if not_s != s]))))
                     for s in steps]))
                safety.append(G(implies(entering_loop, X(conjunct(in_loop, steps[0])))))

                looping_steps = steps + [steps[0]]
                # stepping through loop
                for i in range(1, len(looping_steps)):
                    now = conjunct(looping_steps[i - 1], X(action_sequence[i - 1]))
                    safety.append(G(implies(now, X(conjunct(in_loop, looping_steps[i])))))

                    # stutter
                    now_stutter = conjunct(looping_steps[i - 1], X(stringify_pred(rf_stutter)))
                    safety.append(G(implies(now_stutter, X(conjunct(in_loop, looping_steps[i - 1])))))

                    # other action
                    now_other_change = conjunct(looping_steps[i - 1], X(conjunct(neg(action_sequence[i - 1]),
                                                                                 neg(stringify_pred(rf_stutter)))))
                    safety.append(G(implies(now_other_change, X(neg(in_loop)))))

                if not env_wanted_to_remain_in_loop:
                    # TODO allow_exit needs to allow the environment to choose a certain predicate state (the exit condition)
                    controller_choice = Variable("allow_exit_" + str(len(self.loops)))
                    new_con_variables.append(controller_choice)

                    # at last step, controller can choose to disallow the environment from exiting the loop
                    controller_disallows_exit = conjunct(conjunct(in_loop, steps[-1]), neg(controller_choice))

                    safety.append(G(implies(controller_disallows_exit, X(in_loop))))

                    # to reduce size of game, only allowing controller to set choice variable when at the last step
                    new_guarantees.append(G(implies(neg(steps[-1]), neg(controller_disallows_exit))))

                    new_guarantees.append(
                        G((implies(steps[-1], F(conjunct(env, disjunct(neg(in_loop), controller_choice)))))))
                    new_guarantees.append(
                        G((implies(steps[-1], F(conjunct(con, disjunct(neg(in_loop), controller_choice)))))))
                    # new_guarantees.append(implies(G(F(in_loop)), G(F(neg(in_loop)))))
                else:
                    new_assumptions += [implies(G(F(in_loop)), G(F(neg(in_loop))))]
            else:
                safety.append(G(implies(entering_loop, X(in_loop))))

                now = conjunct(in_loop, X(action_sequence[0]))
                safety.append(G(implies(now, X(in_loop))))

                # stutter
                now_stutter = conjunct(in_loop, X(stringify_pred(rf_stutter)))
                safety.append(G(implies(now_stutter, X(in_loop))))

                # other action
                now_other_change = conjunct(in_loop, X(W(stringify_pred(rf_stutter), conjunct(neg(action_sequence[0]),
                                                                                              neg(stringify_pred(
                                                                                                  rf_stutter))))))
                safety.append(G(implies(now_other_change, X(neg(in_loop)))))

                if not env_wanted_to_remain_in_loop:
                    controller_choice = Variable("allow_exit_" + str(len(self.loops)))
                    new_con_variables.append(controller_choice)

                    # at last step, controller can choose to disallow the environment from exiting the loop
                    controller_disallows_exit = conjunct(in_loop, neg(controller_choice))

                    exit_condition = stringify_formula(exit_predicate_state)
                    safety.append(G(implies(controller_disallows_exit, X(conjunct(in_loop, neg(exit_condition))))))
                    new_state_predicates += [p for p in atomic_predicates(exit_predicate_state)]

                    # to reduce size of game, only allowing controller to set choice variable when at the last step
                    # new_guarantees.append(G(implies(neg(in_loop), X(neg(controller_choice)))))

                    new_guarantees.append(G((implies(in_loop, disjunct(G(con), F(conjunct(env, controller_choice)))))))
                    new_guarantees.append(G((implies(in_loop, disjunct(G(env), F(conjunct(con, controller_choice)))))))
                else:
                    new_assumptions += [implies(G(F(in_loop)), G(F(neg(in_loop))))]

            new_assumptions += safety

            self.loops.append((entry_condition, loop_body, ranking_function))

        return new_env_variables, new_con_variables, new_transition_predicates, new_state_predicates, new_assumptions, new_guarantees

    def initialise(self, debug=True):
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

    def compute_abstract_effect_with_p_new(self, t: Transition, Es, old_effects, predicate):
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

    def compute_abstract_effect_with_p(self, t: Transition, Es, old_effects, predicate):
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
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_pos_Ps += [Ps + [predicate]]

                        # if p was false before, is p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_pos_Ps += [Ps + [neg(predicate)]]

                        # if p was true before, is not p possible next?
                        if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_pos,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
                            new_neg_Ps += [Ps + [(predicate)]]

                        # if p was false before, is not p possible next?
                        if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                    conjunct(formula_neg,
                                                             conjunct_formula_set([add_prev_suffix(P) for P in Ps]))),
                                           self.program.symbol_table):
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

    # this follows the control flow of the program's predicate abstraction
    def add_state_predicates_incrementally(self, state_predicate: Formula, parallelise=True):
        logger.info("Adding state predicate to predicate abstraction:" + str(state_predicate))

        logger.info("Tagging abstract transitions with predicates..")

        done_jobs_env = {}
        done_jobs_con = {}
        jobs = {}

        for t in self.abstract_guard_con.keys() | self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                continue
            jobs[t] = set()
            done_jobs_env[t] = set()
            done_jobs_con[t] = set()

        env_turn = False

        new_abstract_effect = {}
        # residual_abstract_pos_effect = {}
        # residual_abstract_neg_effect = {}
        dealt_with_nows = {}

        for t, E_effects in self.abstract_effect.items():
            new_abstract_effect[t] = {}
            if t not in self.init_program_trans:
                dealt_with_nows[t] = {}
                # residual_abstract_pos_effect[t] = {}
                # residual_abstract_neg_effect[t] = {}
            for E, effects in E_effects.items():
                new_abstract_effect[t][E] = InvertibleMap()
                if t not in self.init_program_trans:
                    dealt_with_nows[t][E] = {}
                    # residual_abstract_pos_effect[t][E] = effects.copy()
                    # residual_abstract_neg_effect[t][E] = effects.copy()

        # add init transitions to jobs
        for t in self.init_program_trans:
            t_formula = transition_formula(t)
            preds_after = set()
            for p in self.state_predicates:
                if p is state_predicate:
                    continue
                if sat(conjunct(p, t_formula), self.program.symbol_table):
                    preds_after.add(p)
                else:
                    preds_after.add(neg(p))
            # this assumes t_formula is satisfiable
            if sat(conjunct(state_predicate, t_formula), self.program.symbol_table):
                pred_val = state_predicate
            else:
                pred_val = neg(state_predicate)

            for E in self.abstract_effect[t].keys():
                new_abstract_effect[t][E].put(frozenset(preds_after | {pred_val}), frozenset({frozenset()}))

            for tt in self.abstract_guard_con.keys():
                if tt.src == t.tgt:
                    if tt in jobs.keys():
                        jobs[tt].add((frozenset(preds_after), pred_val))
                    else:
                        jobs[tt] = {(frozenset(preds_after), pred_val)}

        irrelevant_for_ts = []

        # first, some preprocessing
        for t in self.all_program_trans:
            if t not in self.init_program_trans:
                relevant_preds = {s for _, Rel in self.abstract_effect_relevant_preds[t].items() for s in Rel}
                invars, constants, relevant = self.universal_effect(t, relevant_preds, state_predicate)
                self.abstract_effect_invars[t].extend(invars)
                self.abstract_effect_constant[t].extend(constants)
                if not relevant:
                    irrelevant_for_ts.append(t)

        more_to_do = True
        while more_to_do:
            new_jobs = {}

            if parallelise:
                # TODO there is some non-determinism that causes problems here it seems...
                results = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    # TODO need to prepare pred_state according to t s invars and constants
                    delayed(compute_abstract_effects_with_p_incremental)(t,
                                                                         self.abstract_guard_env_disjuncts[t]
                                                                         if env_turn else
                                                                         self.abstract_guard_con_disjuncts[t],
                                                                         self.abstract_effect_invars[t],
                                                                         self.abstract_effect_constant[t],
                                                                         dealt_with_nows[t],
                                                                         self.abstract_effect[t],
                                                                         # residual_abstract_pos_effect[t],
                                                                         # residual_abstract_neg_effect[t],
                                                                         now_pred_states, state_predicate,
                                                                         self.transition_predicates,
                                                                         t in irrelevant_for_ts,
                                                                         self.abstract_effect_irrelevant_preds[t],
                                                                         self.program.symbol_table)
                    for t, now_pred_states in jobs.items() if len(now_pred_states) > 0)
            else:
                # TODO something wrong when otherRoom is first taken
                results = []
                for t, now_pred_states in jobs.items():
                    if env_turn and t not in self.abstract_guard_env_disjuncts.keys():
                        print()
                    elif not env_turn and t not in self.abstract_guard_con_disjuncts.keys():
                        print()
                    if len(now_pred_states) == 0:
                        continue
                    Es = self.abstract_guard_env_disjuncts[t] if env_turn else self.abstract_guard_con_disjuncts[t]

                    results.append(compute_abstract_effects_with_p_incremental(t, Es,
                                                                               self.abstract_effect_invars[t],
                                                                               self.abstract_effect_constant[t],
                                                                               dealt_with_nows[t],
                                                                               self.abstract_effect[t],
                                                                               # residual_abstract_pos_effect[t],
                                                                               # residual_abstract_neg_effect[t],
                                                                               now_pred_states, state_predicate,
                                                                               self.transition_predicates,
                                                                               t in irrelevant_for_ts,
                                                                               self.abstract_effect_irrelevant_preds[t],
                                                                               self.program.symbol_table))
            next_pred_states = {}
            # use results
            for t, t_formula, Es, dealt_with_nows_t, new_abstract_effects_t, nextPss, new_irrelevant_preds_events in results:
                if t.tgt in next_pred_states.keys():
                    next_pred_states[t.tgt].update(nextPss)
                else:
                    next_pred_states[t.tgt] = nextPss
                if env_turn:
                    self.abstract_guard_env_disjuncts[t] = Es
                else:
                    self.abstract_guard_con_disjuncts[t] = Es
                # dealt_with_nows[t] = dealt_with_nows_t
                # TODO this is not correct, will overwrite everything
                # residual_abstract_pos_effect[t] = residual_abstract_effects_pos_t
                # residual_abstract_neg_effect[t] = residual_abstract_effects_neg_t
                for E in new_abstract_effects_t.keys():
                    for (next, now) in new_abstract_effects_t[E].items():
                        new_abstract_effect[t][E].put_incremental_multiple(next, now)
                    if E in new_irrelevant_preds_events.keys():
                        self.abstract_effect_irrelevant_preds[t][E].update(new_irrelevant_preds_events[E])
                        self.abstract_effect_relevant_preds[t][E].update(
                            {state_predicate} - new_irrelevant_preds_events[E])

            for tgt, nexts in next_pred_states.items():
                if env_turn:
                    transitions = [t for t in self.abstract_guard_con.keys() if t.src == tgt]
                else:
                    transitions = [t for t in self.abstract_guard_env.keys() if
                                   t.src == tgt and t not in self.init_program_trans]

                for t in transitions:
                    t_jobs = set()
                    for nextPs, pred_val in nexts:
                        nextPs_wo_tran_preds = nextPs - set(self.transition_predicates)
                        t_jobs.add((nextPs_wo_tran_preds, pred_val))
                    new_jobs[t] = t_jobs

            if env_turn:
                for t in jobs.keys():
                    done_jobs_env[t].update(jobs[t])
            else:
                for t in jobs.keys():
                    done_jobs_con[t].update(jobs[t])

            more_to_do = False
            for t in jobs.keys():
                if t in new_jobs.keys():
                    if env_turn:
                        jobs[t] = new_jobs[t] - done_jobs_con[t]
                    else:
                        jobs[t] = new_jobs[t] - done_jobs_env[t]
                    if len(jobs[t]) > 0:
                        more_to_do = True
                else:
                    jobs[t].clear()

            env_turn = not env_turn
        self.abstract_effect = new_abstract_effect
        self.state_predicates.append(state_predicate)

        # self.pretty_print_abstract_effect()

    def universal_effect(self, t: Transition, relevant_preds, predicate):
        action = t.action

        vars_modified_in_action_without_identity = [a.left for a in action if not a.left == a.right]
        vars_used_in_action_without_identity = [v for a in action if not a.left == a.right for v in
                                                a.right.variablesin()]
        t_formula = transition_formula(t)

        invars = []
        # consider adding pre_constants
        post_constants = []

        if not any(True for v in predicate.variablesin() if v in vars_modified_in_action_without_identity):
            invars = [predicate]
        elif is_contradictory(conjunct_formula_set([t_formula, (predicate)]), self.program.symbol_table):
            post_constants = [neg(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, neg(predicate)]), self.program.symbol_table):
            post_constants = [(predicate)]
        elif is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(predicate), neg(predicate)]),
                              self.program.symbol_table) and \
                is_contradictory(conjunct_formula_set([t_formula, add_prev_suffix(neg(predicate)), (predicate)]),
                                 self.program.symbol_table):
            invars = [(predicate)]

        # note if relevant to guard
        relevant_for_pre_condition = relevant_pred(t, relevant_preds, predicate)

        return invars, post_constants, relevant_for_pre_condition

    def add_predicates(self, new_state_predicates: [Formula], new_transition_predicates: [Formula],
                       pred_name_dict: dict, simplified: bool, parallelise=True):
        if len(new_state_predicates) + len(new_transition_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")
        logger.info("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()
        self.all_pred_states = set()
        for p in new_state_predicates + new_transition_predicates:
            if parallelise:
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p_new
                results_env = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.compute_abstract_effect_with_p_new)(t, self.abstract_guard_env_disjuncts[t],
                                                                     self.abstract_effect[t], p)
                    for t in self.abstract_guard_env.keys() if t not in self.init_program_trans)
                results_con = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                    delayed(self.compute_abstract_effect_with_p_new)(t, self.abstract_guard_con_disjuncts[t],
                                                                     self.abstract_effect[t], p) for t in
                    self.abstract_guard_con.keys())
            else:
                results_env = []
                for t in self.abstract_guard_env.keys():
                    results_env.append(self.compute_abstract_effect_with_p_new(t, self.abstract_guard_env_disjuncts[t],
                                                                               self.abstract_effect[t], p))

                results_con = []
                for t in self.abstract_guard_con.keys():
                    results_con.append(self.compute_abstract_effect_with_p_new(t, self.abstract_guard_con_disjuncts[t],
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
        self.transition_predicates += new_transition_predicates


    def add_transition_predicates(self, new_transition_predicates: [Formula], pred_name_dict: dict, simplified: bool,
                                  parallelise=True):
        if len(new_transition_predicates) == 0:
            return

        logger.info("Adding predicates to predicate abstraction:")
        logger.info("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()
        self.all_pred_states = set()
        for p in new_transition_predicates:
            if parallelise:
                # shouldn't parallelize here, but the loop within compute_abstract_effect_with_p_new
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

    def allowed_in_abstraction_with_new_pred(self, path: [Transition], new_predicate):
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
            if any(True for v in _action if v.left == _from) \
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

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace_vars(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace_vars(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                          "=", a.right.replace_vars(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                          for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace_vars(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace_vars(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                          "=", a.right.replace_vars(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                          for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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

        exit_trans_is_con = any(True
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
                                                  t.condition.replace_vars(
                                                      lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace_vars(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace_vars(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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
                            And(*conjunct(
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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
                                                  t.condition.replace_vars(
                                                      lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace_vars(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace_vars(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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
                            And(*conjunct(
                                neg(tt.condition.replace_vars(lambda var: Variable(var.name + "_" + str(step)))),
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

powersets = {}
def powerset(S: set):
    if frozenset(S) in powersets.keys():
        return powersets[frozenset(S)]
    else:
        subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
        subsets = sorted(list(map(set, subsets)), key=lambda x: len(x))

        powersets[frozenset(S)] = subsets
        return subsets

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


class InvertibleMap():

    def __init__(self):
        self.dic = dict()  # type : K -> {V} where K and V are frozensets
        self.inv_dic = dict()  # type : V -> {K} where K and V are frozensets

    def __getitem__(self, item):
        return self.dic[item]

    def set(self, dic, inv_dic):
        self.dic = dic
        self.inv_dic = inv_dic

    def copy(self):
        copied = InvertibleMap()
        copied.set(self.dic.copy(), self.inv_dic.copy())
        return copied

    def put(self, key, values):
        if key in self.dic.keys():
            self.dic[key] = (self.dic[key]) | (values)
        else:
            self.dic[key] = values
        for v in values:
            v_as_key = frozenset(v)
            if v_as_key in self.inv_dic.keys():
                self.inv_dic[v_as_key].add(key)
            else:
                self.inv_dic[v_as_key] = {key}

    def put_incremental_single(self, key, value):
        if key in self.dic.keys():
            self.dic[key] = frozenset(self.dic[key] | {value})
        else:
            self.dic[key] = {value}
        v_as_key = frozenset(value)
        if v_as_key in self.inv_dic.keys():
            self.inv_dic[v_as_key].add(key)
        else:
            self.inv_dic[v_as_key] = {key}

    def put_incremental_multiple(self, key, values):
        if key in self.dic.keys():
            self.dic[key] = frozenset(self.dic[key] | set(values))
        else:
            self.dic[key] = values
        for value in values:
            v_as_key = frozenset(value)
            if v_as_key in self.inv_dic.keys():
                self.inv_dic[v_as_key].add(key)
            else:
                self.inv_dic[v_as_key] = {key}

    def get_value(self, key):
        return self.dic[key]

    def get_keys_from_value(self, value):
        return self.inv_dic[value]

    def remove_value_from_keys(self, value):
        if value not in self.inv_dic.keys():
            print()
        relevant_keys = self.inv_dic[value]
        for key in relevant_keys:
            self.dic[key] = frozenset(self.dic[key] - {value})
            if len(self.dic[key]) == 0:
                del self.dic[key]
        del self.inv_dic[value]

    def remove_all_values_from_keys(self, values):
        for v in values:
            self.remove_value_from_keys(v)

    def keep_only_values(self, values):
        relevant_keys = set()
        to_remove = set()
        for v in self.inv_dic.keys():
            if v not in values:
                to_remove.add(v)
            else:
                relevant_keys.update(self.inv_dic[v])
        for v in to_remove:
            del self.inv_dic[v]

        to_remove = set()
        for key in self.dic.keys():
            if key not in relevant_keys:
                to_remove.add(key)
            else:
                new = self.dic[key].intersection(values)
                self.dic[key] = new
        for key in to_remove:
            del self.dic[key]

    def items(self):
        return self.dic.items()

    def items_inverted(self):
        return self.inv_dic.items()

    def keys(self):
        return self.dic.keys()

    def values(self):
        return self.values_single()

    def values_single(self):
        return self.inv_dic.keys()

    def __len__(self):
        return len(self.dic)


def relevant_pred(transition, relevant_preds, predicate):
    # check if relevant for guard
    if any(True for v in predicate.variablesin() if v in transition.condition.variablesin()):
        return True
    # check if used in action (without identities)
    elif any(True for v in predicate.variablesin()
             if any(True for act in transition.action
                    if act.left != act.right
                       and (v == act.left or v in act.right.variablesin()))):
        return True
    elif any(True for v in predicate.variablesin() if any(True for p in relevant_preds if v in p.variablesin())):
        return True
    else:
        return False


def specialise_pred_set(pred_set, invars, state_pred):
    specialised_pred_set = {p for p in pred_set}
    for invar in invars:
        if invar != state_pred:
            specialised_pred_set = specialised_pred_set - {invar}
            specialised_pred_set = specialised_pred_set - {neg(invar)}

    return frozenset(specialised_pred_set)


def complete_pred_set(pred_set, invars, constants, new_predicate, prev_pred_sets):
    complete_pred_sets = set()

    if len(invars) + len(constants) > 0:
        for prev_pred_set in prev_pred_sets:
            complete_pred_set = {p for p in pred_set}

            stop = False
            for invar in invars:
                if invar != new_predicate:
                    if invar in prev_pred_set and neg(invar) not in pred_set:
                        complete_pred_set.add(invar)
                    elif neg(invar) in prev_pred_set and not invar in pred_set:
                        complete_pred_set.add(neg(invar))
                    else:
                        # then prev_pred_set and pred_set are not compatible
                        stop = True
                        break
            if stop:
                continue
            for constant in constants:
                if constant != new_predicate and constant != neg(new_predicate):
                    complete_pred_set.add(constant)
            complete_pred_sets.add(frozenset(complete_pred_set))
    else:
        complete_pred_sets.add(frozenset({p for p in pred_set}))

    return frozenset(complete_pred_sets)


def compute_abstract_effects_with_p_incremental(t: Transition, Es, invars, constants, dealt_with_nows_t, old_effects_t,
                                                prev_pred_states, state_predicate, transition_predicates, irrelevant,
                                                irrelevant_preds_events, symbol_table):
    if len(old_effects_t) == 0:
        return t, transition_formula(t), Es, dealt_with_nows_t, {}, set(), irrelevant_preds_events

    # TODO problem: removing pre condition from residuals, if there is an input pred state that it abstracts
    #   but later on may encounter another refinement of it, preventing continuing the control-flow analysis
    #   consider instead keeping track of the abstractions already considering, and abandoning the control-flow
    #   analysis only when the new input pred state has already been seen

    dict_prev_pred_states = {}
    for nowPs, p in prev_pred_states:
        if nowPs in dict_prev_pred_states.keys():
            dict_prev_pred_states[nowPs].add(p)
        else:
            dict_prev_pred_states[nowPs] = {p}

    # specialised_to_prev_pred_states = {}
    # specialised_prev_pred_states = {}
    # for nowPs, P in dict_prev_pred_states.items():
    #     # this is stupid, a pred state here corresponds to a complete pred state if it is a subset of it
    #     # this is wrong, an invar should not always be removed from now Ps
    #     specialised = nowPs - {p for p in }
    #         # specialise_pred_set(nowPs, invars, state_predicate)
    #     if specialised in specialised_to_prev_pred_states.keys():
    #         specialised_to_prev_pred_states[specialised].add(nowPs)
    #     else:
    #         specialised_to_prev_pred_states[specialised] = {nowPs}
    #     if specialised in specialised_prev_pred_states.keys():
    #         specialised_prev_pred_states[specialised].update(P)
    #     else:
    #         specialised_prev_pred_states[specialised] = P

    # residual_effects_pos_t = {E : effects.copy() for E, effects in old_effects_pos.items()}
    # residual_effects_neg_t = {E : effects.copy() for E, effects in old_effects_neg.items()}
    new_effects_t = {}
    new_irrelevant_preds_events_t = {}

    is_neg_of_pred = lambda x: True if isinstance(x, UniOp) and x.op == "!" else False

    smt_checker = SMTChecker()
    if irrelevant:
        # get all the possible next states from now_pred_state
        for _, E in Es:
            if E not in old_effects_t.keys():
                continue
            new_irrelevant_preds_events_t[E] = {state_predicate}

            nextPss = set()
            new_effects_t[E] = InvertibleMap()
            irrelevant_for_E = irrelevant_preds_events[E] | set(transition_predicates)
            irrelevant_for_E.update({neg(p) for p in irrelevant_for_E})
            # specialised_prev_states_to_E = {}
            # this iteration can probably be moved into the next
            for nowPs, P in dict_prev_pred_states.items():
                newNowPs = (nowPs - irrelevant_for_E)
                # need to add back invars that are relevant for E
                if newNowPs not in old_effects_t[E].values():
                    continue
                # if newNowPs in dealt_with_nows_t[E].keys():
                #     # TODO this is wrong, the concrete pre state, may correspond to an abstract state already dealt with
                #     # but the concrete post state may be different, given invars
                #     newP = P - dealt_with_nows_t[E][newNowPs]
                #     if len(newP) == 0:
                #         continue
                #     else:
                #         if newNowPs in new_dealt_with_nows_t_E.keys():
                #             new_dealt_with_nows_t_E[newNowPs].update(P)
                #         else:
                #             new_dealt_with_nows_t_E[newNowPs] = {p for p in P}
                # else:
                #     if newNowPs in new_dealt_with_nows_t_E.keys():
                #         new_dealt_with_nows_t_E[newNowPs].update(P)
                #     else:
                #         new_dealt_with_nows_t_E[newNowPs] = {p for p in P}

                nextPs = old_effects_t[E].get_keys_from_value(newNowPs)
                for nextP in nextPs:
                    new_effects_t[E].put_incremental_single(nextP, newNowPs)
                    for p in P:
                        nextPss.add((nowPs, nextP, p))

                    # for p in P:
                    #     if p not in invars:
                    #         complete_nowPs = nowPs
                    #     else:
                    #         complete_nowPs = [Ps for Ps in specialised_to_prev_pred_states[nowPs] if p in dict_prev_pred_states[Ps]]
                    #     nextPss.update({(complete_nowPs_instance, nextP, p) for complete_nowPs_instance in complete_nowPs})

            # for nowPs, Preds in specialised_prev_states_to_E.items():
            #     for p in Preds:
            # if is_neg_of_pred(p):
            # oldPss = {Ps_prime for Ps_prime in old_effects_t[E].values_single()
            #           if nowPs.issubset(Ps_prime) and any(
            #         True for Qs in specialised_to_prev_pred_states[nowPs]
            #         if Ps_prime.issubset(Qs))}
            #
            # if E not in residual_effects_neg_t.keys() or len(oldPss) == 0:
            #     continue
            # for oldPs in oldPss:
            # # TODO should i remove this here, or after the for nowPs, Preds loop
            # residual_effects_neg_t[E].remove_all_values_from_keys(oldPss)
            # else:
            #     oldPss = {Ps_prime for Ps_prime in residual_effects_pos_t[E].values_single()
            #               if nowPs.issubset(Ps_prime) and any(
            #             True for Qs in specialised_to_prev_pred_states[nowPs] if Ps_prime.issubset(Qs))}
            #
            #     if E not in residual_effects_pos_t.keys() or len(oldPss) == 0:
            #         continue
            #     residual_effects_pos_t[E].remove_all_values_from_keys(oldPss)
            #
            #     for oldPs in oldPss:
            #         nextPs = old_effects_pos[E].get_keys_from_value(oldPs)
            #         for nextP in nextPs:
            #             new_effects_t[E].put_incremental_single(nextP, oldPs)
            #             nextPss.add((oldPs, nextP, p))

            # for newNowPs in new_dealt_with_nows_t_E.keys():
            #     if newNowPs in dealt_with_nows_t[E].keys():
            #         dealt_with_nows_t[E][newNowPs].update(new_dealt_with_nows_t_E)
            #     else:
            #         dealt_with_nows_t[E][newNowPs] = new_dealt_with_nows_t_E[newNowPs]
        if state_predicate in constants:
            next_pred_states = {(next, state_predicate)
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              [oldPs])}
        elif neg(state_predicate) in constants:
            next_pred_states = {(next, neg(state_predicate))
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              [oldPs])}
        elif state_predicate in invars or neg(state_predicate) in invars:
            next_pred_states = {(next, p)
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              # get only corresponding complete prev states for which p was true before
                                                              [oldPs])}
        else:
            raise Exception(
                "Irrelevant predicate " + str(state_predicate) + " but not in constants or invars, for " + str(t) + ".")

        return t, transition_formula(
            t), Es, dealt_with_nows_t, new_effects_t, next_pred_states, new_irrelevant_preds_events_t
    else:
        action = t.action
        next_pred_states = set()

        t_formula = transition_formula(t)

        new_effects = {}

        new_irrelevant_preds_events = irrelevant_preds_events

        if state_predicate in invars or state_predicate in constants or neg(state_predicate) in constants:
            for (guard_disjunct, E) in Es:
                new_dealt_with_nows_t_E = {}

                formula_pos = add_prev_suffix(conjunct(guard_disjunct, state_predicate))
                if sat(formula_pos, symbol_table, smt_checker):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = add_prev_suffix(conjunct(guard_disjunct, neg(state_predicate)))
                if sat(formula_neg, symbol_table, smt_checker):
                    try_neg = True
                else:
                    try_neg = False

                irrelevant_for_E = irrelevant_preds_events[E] | set(transition_predicates)
                irrelevant_for_E.update({neg(p) for p in irrelevant_for_E})

                newNextPss = InvertibleMap()
                # this iteration can probably be moved into the next
                for nowPs, P in dict_prev_pred_states.items():
                    newNowPs = (nowPs - irrelevant_for_E)
                    if newNowPs not in old_effects_t[E].values():
                        continue
                    # if newNowPs in dealt_with_nows_t[E].keys():
                    #     newP = P - dealt_with_nows_t[E][newNowPs]
                    #     if len(newP) == 0:
                    #         continue
                    #     else:
                    #         if newNowPs in new_dealt_with_nows_t_E.keys():
                    #             new_dealt_with_nows_t_E[newNowPs].update(P)
                    #         else:
                    #             new_dealt_with_nows_t_E[newNowPs] = {p for p in P}
                    # else:
                    #     if newNowPs in new_dealt_with_nows_t_E.keys():
                    #         new_dealt_with_nows_t_E[newNowPs].update(P)
                    #     else:
                    #         new_dealt_with_nows_t_E[newNowPs] = {p for p in P}

                    if not try_neg:
                        P = P - {neg(state_predicate)}
                    if not try_pos:
                        P = P - {state_predicate}

                    if len(P) == 0:
                        continue

                    # # need to add back invars that are relevant for E
                    # if newNowPs in specialised_prev_states_to_E.keys():
                    #     specialised_prev_states_to_E[newNowPs].update(P)
                    # else:
                    #     specialised_prev_states_to_E[newNowPs] = P

                    # old_effects[E] is an InvertibleMap
                    # for Ps, P in specialised_prev_states_to_E.items():
                    for p in P:
                        # if is_neg_of_pred(p):
                        #     oldPss = {Ps_prime for Ps_prime in residual_effects_neg_t[E].values_single()
                        #                 if Ps.issubset(Ps_prime) and any(True for Qs in specialised_to_prev_pred_states[Ps] if Ps_prime.issubset(Qs))}
                        #     if not try_neg or E not in residual_effects_neg_t.keys() or len(oldPss) == 0:
                        #         continue
                        #     residual_effects_neg_t[E].remove_all_values_from_keys(oldPss)
                        # else:
                        #     oldPss = {Ps_prime for Ps_prime in residual_effects_pos_t[E].values_single()
                        #                 if Ps.issubset(Ps_prime) and any(True for Qs in specialised_to_prev_pred_states[Ps] if Ps_prime.issubset(Qs))}
                        #     if not try_pos or E not in residual_effects_pos_t.keys() or len(oldPss) == 0:
                        #         continue
                        #     residual_effects_pos_t[E].remove_all_values_from_keys(oldPss)

                        # consistent_prev_pred_states = [PPs for PPs in specialised_to_prev_pred_states[nowPs]
                        #                                if p in dict_prev_pred_states[PPs]] \
                        #                                 if state_predicate in invars \
                        #                                 else specialised_to_prev_pred_states[nowPs]

                        consistent_prev_pred_states = [nowPs]
                        # for oldPs in oldPss:
                        newPs = newNowPs | {p}

                        next_val = p if state_predicate in invars else neg(
                            state_predicate) if neg(
                            state_predicate) in constants else state_predicate

                        for nextPs in old_effects_t[E].get_keys_from_value(newNowPs):
                            # for (nextPs, Pss) in old_effects[E].items():
                            if not relevant_pred(t, nextPs, state_predicate):
                                new_irrelevant_preds_events_t[E].add(state_predicate)
                                # new_effects[E] = old_effects[E]
                                newNextPss.put_incremental_single(nextPs, newPs)
                                continue
                            if is_neg_of_pred(p):
                                if try_neg and sat(conjunct(conjunct_formula_set(nextPs),
                                                            conjunct(formula_neg,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs, newPs)

                                    next_pred_states.update(
                                        {(next, next_val) for next in complete_pred_set(nextPs, invars, constants,
                                                                                        (state_predicate),
                                                                                        consistent_prev_pred_states)})

                            else:
                                if try_pos and sat(conjunct(conjunct_formula_set(nextPs),
                                                            conjunct(formula_pos,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs, newPs)
                                    next_pred_states.update(
                                        {(next, next_val) for next in complete_pred_set(nextPs, invars, constants,
                                                                                        (state_predicate),
                                                                                        consistent_prev_pred_states)})

                # for newNowPs in new_dealt_with_nows_t_E.keys():
                #     if newNowPs in dealt_with_nows_t[E].keys():
                #         dealt_with_nows_t[E][newNowPs].update(new_dealt_with_nows_t_E)
                #     else:
                #         dealt_with_nows_t[E][newNowPs] = new_dealt_with_nows_t_E[newNowPs]

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    print()

            return t, transition_formula(
                t), Es, dealt_with_nows_t, new_effects, next_pred_states, new_irrelevant_preds_events_t
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            prev_predicate = add_prev_suffix(state_predicate)
            for (guard_disjunct, E) in Es:
                new_dealt_with_nows_t_E = {}

                irrelevant_for_E = irrelevant_preds_events[E] | set(transition_predicates)
                irrelevant_for_E.update({neg(p) for p in irrelevant_for_E})

                # E_formula = add_prev_suffix(conjunct_formula_set(E))
                new_formula = conjunct(action_formula, add_prev_suffix(guard_disjunct))
                formula_pos = conjunct(new_formula, prev_predicate)
                if sat(formula_pos, symbol_table, smt_checker):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = conjunct(new_formula, neg(prev_predicate))
                if sat(formula_neg, symbol_table, smt_checker):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()

                for nowPs, P in dict_prev_pred_states.items():
                    newNowPs = (nowPs - irrelevant_for_E)
                    if newNowPs not in old_effects_t[E].values():
                        continue
                    # if newNowPs in dealt_with_nows_t[E].keys():
                    #     newP = P - dealt_with_nows_t[E][newNowPs]
                    #     if len(newP) == 0:
                    #         continue
                    #     else:
                    #         if newNowPs in new_dealt_with_nows_t_E.keys():
                    #             new_dealt_with_nows_t_E[newNowPs].update(P)
                    #         else:
                    #             new_dealt_with_nows_t_E[newNowPs] = {p for p in P}
                    # else:
                    #     if newNowPs in new_dealt_with_nows_t_E.keys():
                    #         new_dealt_with_nows_t_E[newNowPs].update(P)
                    #     else:
                    #         new_dealt_with_nows_t_E[newNowPs] = {p for p in P}

                    if not try_neg:
                        P = P - {neg(state_predicate)}
                    if not try_pos:
                        P = P - {state_predicate}

                    if len(P) == 0:
                        continue
                    # old_effects[E] is an InvertibleMap
                    # for (nextPs, Pss) in old_effects[E].items():
                    # for Ps, P in specialised_prev_states_to_E.items():
                    for p in P:
                        for nextPs in old_effects_t[E].get_keys_from_value(newNowPs):
                            nextPs_with_p = frozenset(nextPs | {state_predicate})
                            nextPs_with_neg_p = frozenset(nextPs | {neg(state_predicate)})

                            if is_neg_of_pred(p):
                                # if p was false before, is p possible next?
                                if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                            conjunct(formula_neg,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newNowPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs_with_p, newNowPs | {neg(state_predicate)})
                                    next_pred_states.update({(next, (state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate), [nowPs])})

                                # if p was false before, is not p possible next?
                                if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                            conjunct(formula_neg,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newNowPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs_with_neg_p,
                                                                      newNowPs | {neg(state_predicate)})
                                    next_pred_states.update({(next, neg(state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate), [nowPs])})
                            else:
                                # if p was true before, is p possible next?
                                if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                            conjunct(formula_pos,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newNowPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs_with_p, newNowPs | {(state_predicate)})
                                    next_pred_states.update({(next, (state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate), [nowPs])})

                                # if p was true before, is not p possible next?
                                if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                            conjunct(formula_pos,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in newNowPs]))),
                                                   symbol_table, smt_checker):
                                    newNextPss.put_incremental_single(nextPs_with_neg_p, newNowPs | {(state_predicate)})
                                    next_pred_states.update({(next, neg(state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate), [nowPs])})

                # for newNowPs in new_dealt_with_nows_t_E.keys():
                #     if newNowPs in dealt_with_nows_t[E].keys():
                #         dealt_with_nows_t[E][newNowPs].update(new_dealt_with_nows_t_E)
                #     else:
                #         dealt_with_nows_t[E][newNowPs] = new_dealt_with_nows_t_E[newNowPs]

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    print()

            return t, t_formula, Es, dealt_with_nows_t, new_effects, next_pred_states, new_irrelevant_preds_events_t


def compute_abstract_effects_with_p_incremental_old(t: Transition, Es, invars, constants, old_effects_pos,
                                                    old_effects_neg,
                                                    prev_pred_states, state_predicate, irrelevant,
                                                    irrelevant_preds_events, symbol_table):
    if len(old_effects_pos) + len(old_effects_neg) == 0:
        return t, transition_formula(t), Es, old_effects_pos, old_effects_neg, {}, set(), irrelevant_preds_events

    nextPss = set()

    dict_prev_pred_states = {}
    for nowPs, p in prev_pred_states:
        if nowPs in dict_prev_pred_states.keys():
            dict_prev_pred_states[nowPs].add(p)
        else:
            dict_prev_pred_states[nowPs] = {p}

    specialised_to_prev_pred_states = {}
    specialised_prev_pred_states = {}
    for nowPs, P in dict_prev_pred_states.items():
        specialised = specialise_pred_set(nowPs, invars, state_predicate)
        if specialised in specialised_to_prev_pred_states.keys():
            specialised_to_prev_pred_states[specialised].add(nowPs)
        else:
            specialised_to_prev_pred_states[specialised] = {nowPs}
        if specialised in specialised_prev_pred_states.keys():
            specialised_prev_pred_states[specialised].update(P)
        else:
            specialised_prev_pred_states[specialised] = P

    residual_effects_pos_t = {E: effects.copy() for E, effects in old_effects_pos.items()}
    residual_effects_neg_t = {E: effects.copy() for E, effects in old_effects_neg.items()}
    new_effects_t = {}

    is_neg_of_pred = lambda x: True if isinstance(x, UniOp) and x.op == "!" else False

    if irrelevant:
        # get all the possible next states from now_pred_state
        for _, E in Es:
            new_effects_t[E] = InvertibleMap()
            for nowPs, Preds in specialised_prev_pred_states.items():
                for p in Preds:
                    if is_neg_of_pred(p):
                        oldPss = {Ps_prime for Ps_prime in residual_effects_neg_t[E].values_single()
                                  if nowPs.issubset(Ps_prime) and any(
                                True for Qs in specialised_to_prev_pred_states[nowPs]
                                if Ps_prime.issubset(Qs))}

                        if E not in residual_effects_neg_t.keys() or len(oldPss) == 0:
                            continue
                        for oldPs in oldPss:
                            nextPs = old_effects_neg[E].get_keys_from_value(oldPs)
                            for nextP in nextPs:
                                new_effects_t[E].put_incremental_single(nextP, oldPs)
                                nextPss.add((oldPs, nextP, p))
                        # TODO should i remove this here, or after the for nowPs, Preds loop
                        residual_effects_neg_t[E].remove_all_values_from_keys(oldPss)
                    else:
                        oldPss = {Ps_prime for Ps_prime in residual_effects_pos_t[E].values_single()
                                  if nowPs.issubset(Ps_prime) and any(
                                True for Qs in specialised_to_prev_pred_states[nowPs] if Ps_prime.issubset(Qs))}

                        if E not in residual_effects_pos_t.keys() or len(oldPss) == 0:
                            continue
                        residual_effects_pos_t[E].remove_all_values_from_keys(oldPss)

                        for oldPs in oldPss:
                            nextPs = old_effects_pos[E].get_keys_from_value(oldPs)
                            for nextP in nextPs:
                                new_effects_t[E].put_incremental_single(nextP, oldPs)
                                nextPss.add((oldPs, nextP, p))

        if state_predicate in constants:
            next_pred_states = {(next, state_predicate)
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              specialised_to_prev_pred_states[oldPs])}
        elif neg(state_predicate) in constants:
            next_pred_states = {(next, neg(state_predicate))
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              specialised_to_prev_pred_states[oldPs])}
        elif state_predicate in invars or neg(state_predicate) in invars:
            next_pred_states = {(next, p)
                                for oldPs, nextPs, p in nextPss
                                for next in complete_pred_set(nextPs, invars, constants, state_predicate,
                                                              # get only corresponding complete prev states for which p was true before
                                                              [Ps for Ps in specialised_to_prev_pred_states[oldPs]
                                                               if p in dict_prev_pred_states[Ps]])}
        else:
            raise Exception(
                "Irrelevant predicate " + str(state_predicate) + " but not in constants or invars, for " + str(t) + ".")

        return t, transition_formula(
            t), Es, residual_effects_pos_t, residual_effects_neg_t, new_effects_t, next_pred_states, irrelevant_preds_events
    else:
        action = t.action
        next_pred_states = set()

        t_formula = transition_formula(t)

        new_effects = {}

        new_irrelevant_preds_events = irrelevant_preds_events

        if state_predicate in invars or state_predicate in constants or neg(state_predicate) in constants:
            for (guard_disjunct, E) in Es:
                irrelevant_for_E = irrelevant_preds_events[E]
                irrelevant_for_E.update({neg(p) for p in irrelevant_for_E})
                specialised_prev_states_to_E = {}
                # this iteration can probably be moved into the next
                for nowPs, P in specialised_prev_pred_states.items():
                    newNowPs = (nowPs - irrelevant_for_E)
                    # need to add back invars that are relevant for E
                    if newNowPs in specialised_prev_states_to_E.keys():
                        specialised_prev_states_to_E[newNowPs].update(P)
                    else:
                        specialised_prev_states_to_E[newNowPs] = P

                formula_pos = add_prev_suffix(conjunct(guard_disjunct, state_predicate))
                if sat(formula_pos, symbol_table):
                    try_pos = True
                else:
                    try_pos = False

                formula_neg = add_prev_suffix(conjunct(guard_disjunct, neg(state_predicate)))
                if sat(formula_neg, symbol_table):
                    try_neg = True
                else:
                    try_neg = False
                newNextPss = InvertibleMap()
                # old_effects[E] is an InvertibleMap
                for Ps, P in specialised_prev_states_to_E.items():
                    for p in P:
                        if is_neg_of_pred(p):
                            oldPss = {Ps_prime for Ps_prime in residual_effects_neg_t[E].values_single()
                                      if Ps.issubset(Ps_prime) and any(
                                    True for Qs in specialised_to_prev_pred_states[Ps] if Ps_prime.issubset(Qs))}
                            if not try_neg or E not in residual_effects_neg_t.keys() or len(oldPss) == 0:
                                continue
                            residual_effects_neg_t[E].remove_all_values_from_keys(oldPss)
                        else:
                            oldPss = {Ps_prime for Ps_prime in residual_effects_pos_t[E].values_single()
                                      if Ps.issubset(Ps_prime) and any(
                                    True for Qs in specialised_to_prev_pred_states[Ps] if Ps_prime.issubset(Qs))}
                            if not try_pos or E not in residual_effects_pos_t.keys() or len(oldPss) == 0:
                                continue
                            residual_effects_pos_t[E].remove_all_values_from_keys(oldPss)

                        for oldPs in oldPss:
                            newPs = oldPs | {p}

                            next_val = p if state_predicate in invars else neg(
                                state_predicate) if neg(
                                state_predicate) in constants else state_predicate

                            old_effects = old_effects_neg if is_neg_of_pred(p) else old_effects_pos
                            for nextPs in old_effects[E].get_keys_from_value(oldPs):
                                # for (nextPs, Pss) in old_effects[E].items():
                                if not relevant_pred(t, nextPs, state_predicate):
                                    new_irrelevant_preds_events[E].append(state_predicate)
                                    # new_effects[E] = old_effects[E]
                                    newNextPss.put_incremental_single(nextPs, newPs)
                                    continue
                                if is_neg_of_pred(p):
                                    if try_neg and sat(conjunct(conjunct_formula_set(nextPs),
                                                                conjunct(formula_neg,
                                                                         conjunct_formula_set(
                                                                             [add_prev_suffix(P) for P in newPs]))),
                                                       symbol_table):
                                        newNextPss.put_incremental_single(nextPs, newPs)

                                        next_pred_states.update(
                                            {(next, next_val) for next in complete_pred_set(nextPs, invars, constants,
                                                                                            (state_predicate),
                                                                                            specialised_to_prev_pred_states[
                                                                                                Ps])})

                                else:
                                    if try_pos and sat(conjunct(conjunct_formula_set(nextPs),
                                                                conjunct(formula_pos,
                                                                         conjunct_formula_set(
                                                                             [add_prev_suffix(P) for P in newPs]))),
                                                       symbol_table):
                                        newNextPss.put_incremental_single(nextPs, newPs)
                                        next_pred_states.update(
                                            {(next, next_val) for next in complete_pred_set(nextPs, invars, constants,
                                                                                            (state_predicate),
                                                                                            specialised_to_prev_pred_states[
                                                                                                Ps])})

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    print()

            return t, transition_formula(
                t), Es, residual_effects_pos_t, residual_effects_neg_t, new_effects, next_pred_states, new_irrelevant_preds_events
        else:
            action_formula = conjunct_formula_set([BiOp(a.left, "=", add_prev_suffix(a.right)) for a in action])
            prev_predicate = add_prev_suffix(state_predicate)
            for (guard_disjunct, E) in Es:
                irrelevant_for_E = irrelevant_preds_events[E]
                irrelevant_for_E.update({neg(p) for p in irrelevant_for_E})
                specialised_prev_states_to_E = {(nowPs - irrelevant_for_E): p for nowPs, p in
                                                specialised_prev_pred_states.items()}

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
                # for (nextPs, Pss) in old_effects[E].items():
                for Ps, P in specialised_prev_states_to_E.items():
                    for p in P:
                        if is_neg_of_pred(p):
                            if not try_neg or E not in residual_effects_neg_t.keys() or Ps not in \
                                    residual_effects_neg_t[E].values_single():
                                continue
                            residual_effects_neg_t[E].remove_value_from_keys(Ps)
                        else:
                            if not try_pos or E not in residual_effects_pos_t.keys() or Ps not in \
                                    residual_effects_pos_t[E].values_single():
                                continue
                            residual_effects_pos_t[E].remove_value_from_keys(Ps)

                        old_effects = old_effects_neg if is_neg_of_pred(p) else old_effects_pos
                        for nextPs in old_effects[E].get_keys_from_value(Ps):
                            nextPs_with_p = frozenset(nextPs | {state_predicate})
                            nextPs_with_neg_p = frozenset(nextPs | {neg(state_predicate)})

                            if is_neg_of_pred(p):
                                # if p was false before, is p possible next?
                                if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                            conjunct(formula_neg,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in Ps]))),
                                                   symbol_table):
                                    newNextPss.put_incremental_single(nextPs_with_p, Ps | {neg(state_predicate)})
                                    next_pred_states.update({(next, (state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate),
                                                                               specialised_to_prev_pred_states[Ps])})

                                # if p was false before, is not p possible next?
                                if try_neg and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                            conjunct(formula_neg,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in Ps]))),
                                                   symbol_table):
                                    newNextPss.put_incremental_single(nextPs_with_neg_p, Ps | {neg(state_predicate)})
                                    next_pred_states.update({(next, neg(state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate),
                                                                               specialised_to_prev_pred_states[Ps])})
                            else:
                                # if p was true before, is p possible next?
                                if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_p),
                                                            conjunct(formula_pos,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in Ps]))),
                                                   symbol_table):
                                    newNextPss.put_incremental_single(nextPs_with_p, Ps | {(state_predicate)})
                                    next_pred_states.update({(next, (state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate),
                                                                               specialised_to_prev_pred_states[Ps])})

                                # if p was true before, is not p possible next?
                                if try_pos and sat(conjunct(conjunct_formula_set(nextPs_with_neg_p),
                                                            conjunct(formula_pos,
                                                                     conjunct_formula_set(
                                                                         [add_prev_suffix(P) for P in Ps]))),
                                                   symbol_table):
                                    newNextPss.put_incremental_single(nextPs_with_neg_p, Ps | {(state_predicate)})
                                    next_pred_states.update({(next, neg(state_predicate)) for next in
                                                             complete_pred_set(nextPs, invars, constants,
                                                                               (state_predicate),
                                                                               specialised_to_prev_pred_states[Ps])})

                if len(newNextPss) > 0:
                    new_effects[E] = newNextPss
                else:
                    print()

            return t, t_formula, Es, residual_effects_pos_t, residual_effects_neg_t, new_effects, next_pred_states, new_irrelevant_preds_events


def merge_transitions(transitions: [Transition], symbol_table, to_program_transitions):
    # can probably do this while building the initial abstraction
    new_transitions = []
    new_to_program_transitions = {}

    # partition the transitions into classes where in each class each transition has the same outputs and source and end state
    partitions = dict()
    for transition in transitions:
        key = str(transition.src) + str(
            conjunct_formula_set(sorted(transition.output, key=lambda x: str(x)))) + str(
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
            conditions_simplified_fnode = conditions_smt  # simplify(conditions_smt)#.simplify()
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