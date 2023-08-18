from graphviz import Digraph
from pysmt.shortcuts import And

from programs.abstraction.effects_abstraction.util.effects_util import tran_and_state_preds_after_con_env_step
from programs.abstraction.explicit_abstraction.util.abstract_state import AbstractState
from programs.abstraction.interface.predicate_abstraction import PredicateAbstraction
from programs.analysis.compatibility_checking.nuxmv_model import NuXmvModel
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, neg, conjunct, mutually_exclusive_rules, \
    propagate_negations, dnf
from prop_lang.variable import Variable


class MealyMachine:
    def __init__(self, name, init_st: int, env_events, con_events, env_transitions={}, con_transitions={}):
        self.name = name
        self.init_st = str(init_st)
        self.states = {self.init_st} | {k for k in env_transitions.keys() | con_transitions.keys()}
        self.env_events = env_events
        self.con_events = con_events
        self.env_transitions = env_transitions
        self.con_transitions = con_transitions
        self.counter = -1

    def add_transitions(self, trans_dict: dict):
        int_st_index = 0
        interm_states = {}
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            new_src = "st_" + str(src_index)

            env_cond = (env_behaviour.simplify()).to_nuxmv()
            env_cond = propagate_negations(env_cond)

            con_behaviour = disjunct_formula_set(trans_dict[(src_index, env_behaviour, tgt_index)])
            con_cond = (con_behaviour.simplify()).to_nuxmv()
            con_cond = propagate_negations(con_cond)
            con_cond_dnf = dnf(con_cond, simplify=False)
            if isinstance(con_cond_dnf, BiOp) and con_cond_dnf.op[0] == "|":
                con_conds = con_cond_dnf.sub_formulas_up_to_associativity()
            else:
                con_conds = [con_cond_dnf]

            new_tgt = "st_" + str(tgt_index)

            if new_src not in self.env_transitions.keys():
                self.env_transitions[new_src] = set()

            if (env_cond, new_src) in interm_states.keys():
                new_intermed = interm_states.get((env_cond, new_src))
            else:
                new_intermed = "st__" + str(int_st_index)
                interm_states[(env_cond, new_src)] = new_intermed
                int_st_index += 1
                self.con_transitions[new_intermed] = set()

            if (env_cond, new_intermed) not in self.env_transitions[new_src]:
                self.env_transitions[new_src].add((env_cond, new_intermed))

            for cond in con_conds:
                if (cond, new_tgt) not in self.con_transitions[new_intermed]:
                    self.con_transitions[new_intermed] |= {(cond, new_tgt)}

            self.states.add(new_intermed)
            self.counter = self.counter - 1
            self.states.add(new_src)
            self.states.add(new_tgt)

    def __str__(self):
        return str(self.to_dot())

    def to_dot(self, pred_list: [Formula] = None):
        to_replace = []
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace += [BiOp(pred_var, ":=", pred)]


        dot = Digraph(name="MealyMachine",
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"),  # ("rankdir", "LR"),
                                  ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "circle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            dot.node(str(s))

        dot.edge("init", str(self.init_st), style="solid")

        for src in self.env_transitions.keys():
            for (beh, tgt) in self.env_transitions.get(src):
                label = str(beh.replace(to_replace))
                dot.edge(str(src), str(tgt), label)

        for src in self.con_transitions.keys():
            for (beh, tgt) in self.con_transitions.get(src):
                label = str(beh.replace(to_replace))
                dot.edge(str(src), str(tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self, mon_states, mon_out_events, state_pred_list, trans_pred_list):
        state_pred_acts = [label_pred(p, state_pred_list) for p in state_pred_list]
        trans_pred_acts = [label_pred(p, trans_pred_list) for p in trans_pred_list]
        pred_acts = state_pred_acts + trans_pred_acts

        mon_events = mon_out_events \
                     + [Variable(s) for s in mon_states]

        new_mon_events = [BiOp(m, ":=", Variable("mon_" + m.name)) for m in mon_events] \
                         + [BiOp(m, ":=", Variable(m.name)) for m in pred_acts]

        guards_acts = {}

        init_conds = []

        for (env_beh, tgt) in self.env_transitions.get(self.init_st):
            formula_set = [env_beh.replace(new_mon_events), Variable(tgt)] + [neg(Variable(st)) for st in self.states if st != tgt]
            init_conds += [conjunct_formula_set(formula_set)]

        init_cond = disjunct_formula_set(init_conds)
        for src in self.con_transitions.keys():
            for (con_behaviour, con_tgt) in self.con_transitions[src]:
                guard = "turn = mon_env & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()
                act = "next(" + str(con_behaviour.replace(new_mon_events).to_nuxmv()) + " & " + str(con_tgt) + \
                      " & " + " & ".join(["!" + st for st in self.states if st != con_tgt] +
                                         ["!" + str(o) for o in mon_out_events]) + ")"
                guards_acts[guard].append(act)
                if (con_tgt not in self.env_transitions.keys()) or len(self.env_transitions.get(con_tgt)) == 0:
                    raise Exception("Nothing to do in counter-strategy from state " + str(con_tgt))

        for src in self.env_transitions.keys():
            for (env_beh, env_tgt) in self.env_transitions.get(src):
                guard = "turn = mon_con & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()

                act = "next(" + str(env_beh.replace(new_mon_events).to_nuxmv()) + " & " + str(env_tgt) + \
                      " & " + " & ".join(["!" + st for st in self.states if st != env_tgt]) + ")"

                guards_acts[guard].append(act)

        define = []
        transitions = []
        guard_ids = []
        i = 0
        guard_keys = list(guards_acts.keys())
        while i < len(guard_keys):
            define += [self.name + "_guard_" + str(i) + " := " + guard_keys[i]]
            define += [
                self.name + "_act_" + str(i) + " := (" + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]])) + ")"]
            transitions.append(self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i))
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["next(" + str(event) + ") = " + str(event) for event in (self.env_events + self.con_events) if
                     Variable(str(event)) not in (mon_events + pred_acts)]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name + "& next(mismatch)")

        vars = ["turn : {env, mon_env, con, mon_con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(var) + " : boolean" for var in self.env_events if
                 str(var) not in [str(v) for v in (mon_events + pred_acts)]]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["mon_" + str(var) + " : boolean" for var in mon_events]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions = ["((" + ")\n\t|\t(".join(transitions) + "))"]

        identity = "((turn = env | turn = con) -> (identity_" + self.name + " & " + str(conjunct_formula_set(
            [BiOp(UniOp("next", Variable("mon_" + e.name)), "=", Variable("mon_" + e.name)) for e in
             mon_events] +
            [BiOp(UniOp("next", Variable(p.name)), "=", Variable(p.name)) for p in
             pred_acts]).to_nuxmv()) + "))"

        trans = ["(" + identity + " &\n\t\t(!(turn = env | turn = con) -> (" + ")\n\t|\t(".join(transitions) + ")))"]
        # invar = mutually_exclusive_rules(self.states)
        invar = mutually_exclusive_rules(["mon_" + s for s in mon_states])
        # invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]
        # j = 0
        # while j < len(trans_pred_acts):
        #     invar += [str(neg(conjunct(trans_pred_acts[j], trans_pred_acts[j + 1])))]
        #     j += 2

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    def fill_in_predicates_at_controller_states_label_tran_preds_appropriately(self, predicate_abstraction, program, abstract_program):
        symbol_table = (program.symbol_table |
                        {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation})

        new_con_transitions = {k:{} for k, _ in self.con_transitions.items()}
        new_env_transitions = {k:{} for k, _ in self.env_transitions.items()}

        smt_checker = SMTChecker()

        pred_list = predicate_abstraction.get_state_predicates() + predicate_abstraction.get_transition_predicates()

        replace_preds = []
        i = 0
        for p in pred_list:
            label = label_pred(p, pred_list)
            symbol_table[label.name] = TypedValuation(label.name, "boolean", False)
            replace_preds.append(BiOp(Variable(label.name), ":=", p))
            i += 1

        at_least_one_state = disjunct_formula_set([Variable(q) for q in program.states])

        at_most_one_state = conjunct_formula_set([BiOp(Variable(q), "=>",
                                                       conjunct_formula_set([neg(Variable(r))
                                                                             for r in program.states
                                                                             if r != q]))
                                                  for q in program.states])
        current_states = []

        abstraction = abstract_program
        # abstraction = predicate_abstraction.py.simplified_transitions_abstraction()

        for (m_cond, mm_tgt) in self.env_transitions[self.init_st]:
            for pa_t in abstraction.state_to_env[abstraction.initial_state]:
                formula = conjunct_formula_set(
                    [m_cond.replace(replace_preds), pa_t.condition, at_least_one_state, at_most_one_state,
                     Variable(pa_t.tgt.state)] +
                    pa_t.tgt.predicates +
                    pa_t.output).replace(replace_preds)
                formula_smt = And(*formula.to_smt(symbol_table))
                compatible = smt_checker.check(formula_smt)
                if compatible:
                    current_states.append((mm_tgt, pa_t.tgt))
                    new_env_transitions[self.init_st][(m_cond, mm_tgt)] = {}

        done_states = [(self.init_st, abstraction.initial_state)]

        def concretize_state(abstract_states, conretish_state, symbol_table):
            conretish_states = []

            for abstracter_state in abstract_states:
                if not isinstance(abstracter_state, str) and abstracter_state.compatible(conretish_state, symbol_table):
                    conretish_states.append(abstracter_state)
            return conretish_states

        def concretize_transition(predicate_abstraction, transition, src_preds):
            tgt_preds = []
            for src_pred in src_preds:
                if src_pred not in transition.tgt.predicates and \
                    neg(src_pred) not in transition.tgt.predicates:
                    tgt_preds.append(src_pred)
            tgt_preds.extend(transition.tgt.predicates)
            new_src = AbstractState(transition.src.state, src_preds)
            new_tgt = AbstractState(transition.tgt.state, tgt_preds)
            return Transition(new_src, transition.condition, transition.action, transition.output, new_tgt)


        # TODO this needs to be optimised
        while len(current_states) > 0:
            next_states = []
            for (mm_con_src, pa_con_src) in current_states:
                tentative_con_trans = []
                for (mm_con_cond, mm_con_tgt) in self.con_transitions[mm_con_src]:
                    # TODO this can be optimised by keeping a cache
                    abstract_pa_con_srcs = concretize_state(abstraction.state_to_con.keys(), pa_con_src, symbol_table)

                    for abstract_pa_con_src in abstract_pa_con_srcs:
                        for pa_con_t in abstraction.state_to_con[abstract_pa_con_src]:
                            formula = conjunct_formula_set(
                                [mm_con_cond.replace(replace_preds), pa_con_t.condition]).replace(replace_preds)
                            formula_smt = And(*formula.to_smt(symbol_table))
                            compatible = smt_checker.check(formula_smt)
                            if compatible:
                                if abstract_pa_con_src != pa_con_src:
                                    new_pa_con_t = concretize_transition(predicate_abstraction, pa_con_t, pa_con_src.predicates)
                                else:
                                    new_pa_con_t = pa_con_t
                                tentative_con_trans.append((mm_con_cond, mm_con_tgt, new_pa_con_t))

                for (mm_con_cond, mm_con_tgt, pa_con_t) in tentative_con_trans:
                    (mm_env_src, pa_env_src) = (mm_con_tgt, pa_con_t.tgt)
                    abstract_pa_env_srcs = concretize_state(abstraction.state_to_env.keys(), pa_env_src,
                                                               symbol_table)

                    for (mm_env_cond, mm_env_tgt) in self.env_transitions[mm_env_src]:
                        for abstract_pa_env_src in abstract_pa_env_srcs:
                            for pa_env_t in abstraction.state_to_env[abstract_pa_env_src]:
                                try:
                                    f_trans_preds = tran_and_state_preds_after_con_env_step(pa_env_t)
                                    formula2 = conjunct_formula_set([mm_env_cond.replace(replace_preds)] +
                                                                    [pa_env_t.condition] +
                                                                    pa_env_t.output +
                                                                    [Variable(pa_env_t.tgt.state)] +
                                                                    [at_least_one_state] +
                                                                    [at_most_one_state] +
                                                                    f_trans_preds)
                                    formula2_smt = And(*formula2.to_smt(symbol_table))
                                    compatible = smt_checker.check(formula2_smt)
                                    if compatible:
                                        next_states.append((mm_env_tgt, pa_env_t.tgt))
                                        if (mm_con_cond, mm_con_tgt) not in new_con_transitions[mm_con_src].keys():
                                            new_con_transitions[mm_con_src][(mm_con_cond, mm_con_tgt)] = set()
                                        new_con_transitions[mm_con_src][(mm_con_cond, mm_con_tgt)] |= {conjunct_formula_set([Variable(pa_env_src.state)] + [label_pred(p, pred_list) for p in pa_env_t.src.predicates])}

                                        # TODO repair transition predicates
                                        new_env_transitions[mm_env_src][(mm_env_cond, mm_env_tgt)] = {}
                                except Exception as e:
                                    raise e

            done_states += [str(s) for s in current_states]
            current_states = set([x for x in next_states if str(x) not in done_states])

        proper_con_transitions = {k:set() for (k, _) in new_con_transitions.items()}
        for k, dict in new_con_transitions.items():
            for (mm_con_cond, mm_con_tgt) in dict.keys():
                proper_con_transitions[k] |= {(conjunct(mm_con_cond, disjunct_formula_set(dict[(mm_con_cond, mm_con_tgt)])), (mm_con_tgt))}

        return MealyMachine(self.name, self.init_st, self.env_events, self.con_events, self.env_transitions, proper_con_transitions)

    # TODO this function needs to be optimised
    def project_controller_on_program(self, name, program, predicate_abstraction: PredicateAbstraction, symbol_table,
                                      program_on_env_side=True, mealy_machine_events_on_transitions=True):
        symbol_table |= {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation}

        new_env_transitions = set()
        new_con_transitions = set()

        smt_checker = SMTChecker()

        pred_list = predicate_abstraction.state_predicates + predicate_abstraction.transition_predicates

        replace_preds = []
        i = 0
        for p in pred_list:
            label = label_pred(p, pred_list)
            replace_preds.append(BiOp(Variable(label.name), ":=", p))
            i += 1

        at_least_one_state = disjunct_formula_set([Variable(q) for q in program.states])

        at_most_one_state = conjunct_formula_set([BiOp(Variable(q), "=>",
                                                       conjunct_formula_set([neg(Variable(r))
                                                                             for r in program.states
                                                                             if r != q]))
                                                  for q in program.states])
        current_states = []
        done_states = []

        abstraction = predicate_abstraction.simplified_transitions_abstraction()

        for (m_cond, mm_tgt) in self.env_transitions[self.init_st]:
            for pa_t in abstraction.state_to_env[abstraction.initial_state]:
                formula = conjunct_formula_set(
                    [m_cond.replace(replace_preds), pa_t.condition, at_least_one_state, at_most_one_state,
                     Variable(pa_t.tgt.state)] +
                    pa_t.tgt.predicates +
                    pa_t.output)
                formula_smt = And(*formula.to_smt(symbol_table))
                compatible = smt_checker.check(formula_smt)
                if compatible:
                    new_env_transitions \
                        .add(
                        Transition((self.init_st, abstraction.initial_state),
                                   pa_t.condition if not mealy_machine_events_on_transitions else m_cond,
                                   pa_t.action,
                                   pa_t.output, (mm_tgt, pa_t.tgt)))
                    current_states.append((mm_tgt, pa_t.tgt))

        done_states += [(self.init_st, abstraction.initial_state)]

        # TODO this needs to be optimised
        while len(current_states) > 0:
            next_states = []
            for (mm_con_src, pa_con_src) in current_states:
                tentative_con_trans = []
                for (mm_con_cond, mm_con_tgt) in self.con_transitions[mm_con_src]:
                    # TODO this can be optimised by keeping a cache
                    for pa_con_t in abstraction.state_to_con[pa_con_src]:
                        formula = conjunct_formula_set(
                            [mm_con_cond.replace(replace_preds), pa_con_t.condition])
                        formula_smt = And(*formula.to_smt(symbol_table))
                        compatible = smt_checker.check(formula_smt)
                        if compatible:
                            tentative_con_trans.append(
                                Transition((mm_con_src, pa_con_src),
                                           mm_con_cond,
                                           pa_con_t.action, pa_con_t.output,
                                           (mm_con_tgt, pa_con_t.tgt)))

                for mm_con_trans in tentative_con_trans:
                    (mm_env_src, pa_env_src) = mm_con_trans.tgt
                    for (mm_env_cond, mm_env_tgt) in self.env_transitions[mm_env_src]:
                        for pa_env_t in abstraction.state_to_env[pa_env_src]:
                            try:
                                f_trans_preds = tran_and_state_preds_after_con_env_step(pa_env_t)
                                formula2 = conjunct_formula_set([mm_env_cond.replace(replace_preds)] +
                                                                [pa_env_t.condition] +
                                                                pa_env_t.output +
                                                                [Variable(pa_env_t.tgt.state)] +
                                                                [at_least_one_state] +
                                                                [at_most_one_state] +
                                                                f_trans_preds)
                                formula2_smt = And(*formula2.to_smt(symbol_table))
                                compatible = smt_checker.check(formula2_smt)
                                if compatible:
                                    next_states.append((mm_env_tgt, pa_env_t.tgt))
                                    new_con_transitions.add(mm_con_trans)
                                    new_env_transitions.add(
                                        Transition((mm_env_src, pa_env_src),
                                                   pa_env_t.condition if not mealy_machine_events_on_transitions else mm_env_cond,
                                                   pa_env_t.action,
                                                   pa_env_t.output, (mm_env_tgt, pa_env_t.tgt)))
                            except Exception as e:
                                raise e

            done_states += [str(s) for s in current_states]
            current_states = set([x for x in next_states if str(x) not in done_states])

        # TODO need to check that if counter-strategy, then it s complete for controller
        #  and if strategy then complete for environment

        return Program(name, [s for t in (new_con_transitions | new_env_transitions) for s in [t.src, t.tgt]],
                       (self.init_st, abstraction.initial_state),
                       abstraction.valuation, list(set(new_env_transitions)), list(set(new_con_transitions)),
                       abstraction.env_events, abstraction.con_events,
                       abstraction.out_events, False)

