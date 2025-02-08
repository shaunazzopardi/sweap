import logging
from multiprocessing import Pool
from typing import Set
from textwrap import dedent

from graphviz import Digraph

import config
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import stutter_transition, symbol_table_from_program, is_deterministic, binary_rep_states, \
    add_prev_suffix
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.util import (disjunct_formula_set, neg, true, \
                            sat, type_constraints_acts, implies, is_tautology, sat_parallel, mutually_exclusive_rules,
                            atomic_predicates,
                            simplify_formula_with_math_wo_type_constraints, conjunct, conjunct_typed_valuation_set,
                            massage_ltl_for_dual)
from prop_lang.value import Value
from prop_lang.variable import Variable


class Program:

    def __init__(self, name, sts, init_st, init_val: [TypedValuation],
                 transitions: [Transition],
                 env_events: [Variable], con_events: [Variable],
                 preprocess=True, is_determ=None):
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.valuation = init_val

        if config.Config.getConfig().dual:
            self.env_events = con_events
            self.con_events = env_events
        else:
            self.env_events = env_events
            self.con_events = con_events
        self.out_events = []
        self.symbol_table = symbol_table_from_program(self)
        self.local_vars = [Variable(tv.name) for tv in init_val]

        self.transitions = transitions

        if len(self.transitions) == 0:
            self.transitions = [Transition(s, true(), [], [], s) for s in self.states]

        logging.info("Processing program.")
        print("Processing program.")
        if preprocess:
            all_vars = self.local_vars
            self.transitions = [t.complete_outputs(self.out_events)
                                    .complete_action_set(all_vars) for t in self.transitions]
            unsat_trans = []
            with Pool(config.Config.getConfig().workers) as pool:
                arg1 = []
                arg2 = []
                for t in self.transitions:
                    arg1.append(t.condition)
                    arg2.append(self.symbol_table)
                results = pool.map(sat_parallel, zip(arg1, arg2))
                new_transitions = []
                for i, t in enumerate(self.transitions):
                    if not results[i]:
                        unsat_trans.append(t)
                    else:
                        new_transitions.append(t)

            if len(unsat_trans) > 0:
                logging.info("Removed transitions with unsat transitions: " + ",\n".join(map(str, unsat_trans)))

        otherwise = [t for t in self.transitions if str(t.condition) == "otherwise"]
        if len(otherwise) > 1:
            raise Exception("Too many environment otherwise transitions")
        elif len(otherwise) == 1:
            otherwise_trans = otherwise[0]
            condition = neg(disjunct_formula_set([t.condition
                                                                  for t in transitions
                                                                  if t.src == otherwise_trans.src
                                                                  and t != otherwise_trans]))
            if sat(condition, self.symbol_table):
                concrete_trans = Transition(otherwise_trans.src,
                                                condition,
                                                otherwise_trans.action,
                                                otherwise_trans.output,
                                                otherwise_trans.tgt)
                self.transitions.append(concrete_trans)
            self.transitions.remove(otherwise_trans)

        self.orig_ts, self.stutter_ts = self.complete_transitions_stutter_explicit()
        self.transitions = self.orig_ts + self.stutter_ts
        # TODO this can take a long time, see concurrent-safety-response
        self.state_to_trans = {}
        for t in self.transitions:
            if t.src in self.state_to_trans.keys():
                self.state_to_trans[t.src].append(t)
            else:
                self.state_to_trans[t.src] = [t]

        self.deterministic = None
        if preprocess:
            if is_determ is None:
                self.deterministic = is_deterministic(self)
            else:
                self._det = None

                def lazy_det(slf):
                    if slf._det is None:
                        slf._det = is_deterministic(slf)
                    return slf._det

                def skip(_):
                    pass
                self.deterministic = property(lazy_det, skip, skip, "")

        self.bin_state_vars, self.states_binary_map = binary_rep_states(self.states)
        self.bin_to_orig_state_map = {st: k for k, st in self.states_binary_map.items()}
        self.states_binary_map |= {Variable(st): bin_st for st, bin_st in self.states_binary_map.items()}

        self.project_out_constants()
        while self.refine_var_types():
            pass

    def refine_var_types(self):
        new_symbol_table = {}
        for n, tv in self.symbol_table.items():
            if tv.type.startswith("int"):
                v = Variable(tv.name)
                nat_pred = BiOp(v, ">=", Value("0"))
                if not is_tautology(implies(conjunct_typed_valuation_set(self.valuation), nat_pred), self.symbol_table):
                    continue
                symbol_table_with_prevs = {(m + "_prev") : TypedValuation(m + "_preb", tv.type, tv.value) for m, tv in self.symbol_table.items()}
                exit = False
                prev_nat = add_prev_suffix(nat_pred)
                for t in self.transitions:
                    if not is_tautology(implies(conjunct(prev_nat, t.formula()), nat_pred), self.symbol_table | symbol_table_with_prevs):
                        exit = True
                        break
                if not exit:
                    print("turned " + n + " into a natural")
                    new_symbol_table[n] = TypedValuation(n, "natural", tv.value)

        self.symbol_table.update(new_symbol_table)
        return len(new_symbol_table) > 0

    def project_out_constants(self):
        vars_to_project_out = {}
        stutter_acts = []
        new_valuation = []
        for tv in self.valuation:
            if all(BiOp(Variable(tv.name), ":=", Variable(tv.name)) in t.action for t in self.transitions):
                vars_to_project_out[Variable(tv.name)] = Value(tv.value)
                stutter_acts.append(BiOp(Variable(tv.name), ":=", Variable(tv.name)))
            else:
                new_valuation.append(tv)

        if len(vars_to_project_out.keys()) == 0:
            return

        for t in self.transitions:
            t.action = [a for a in t.action if a.left not in vars_to_project_out.keys()]
            preds_in_cond = atomic_predicates(t.condition)
            preds_to_replace = {p: simplify_formula_with_math_wo_type_constraints(p.replace_formulas(vars_to_project_out), self.symbol_table)
                                for p in preds_in_cond if not vars_to_project_out.keys().isdisjoint(p.variablesin())}
            t.condition = t.condition.replace_formulas(preds_to_replace)

        for v in vars_to_project_out.keys():
            del self.symbol_table[v.name]
            del self.symbol_table[v.name + "_prev"]
            del self.symbol_table[v.name + "_prev_prev"]

        self.valuation = new_valuation
        self.local_vars = [Variable(tv.name) for tv in new_valuation]


    def add_type_constraints_to_guards(self, transition: Transition):
        constraints = type_constraints_acts(transition, self.symbol_table).to_nuxmv()
        if not is_tautology(implies(transition.condition, constraints), self.symbol_table):
            return transition.add_condition(constraints)
        else:
            return transition

    def is_finite_state(self):
        return all(val.is_finite_state() for val in self.symbol_table.values())

    def to_prog(self, spec=None):
        def state_to_str(x):
            if not isinstance(x, str) and hasattr(x, "__iter__"):
                return ", ".join(str[v] for v in list(x))
            return str(x)

        def fmt_valuation(v: TypedValuation):
            typ = {
                "int": "integer", "nat": "integer", "natural": "integer",
                "bool": "boolean"}.get(str(v.type), str(v.type))
            return f"{v.name} : {typ} := {str(v.value).lower()}"

        def tr_to_str(t, is_env):
            def remove_paren(s):
                s1 = str(s)
                return s1[1:-1] if s1.startswith('(') else s1

            result = f"{state_to_str(t.src)} -> {state_to_str(t.tgt)} [{remove_paren(t.condition)}"  # noqa: E501
            if t.action is not None and len(t.action) > 0:
                result += " $ " + '; '.join(map(remove_paren, t.action))
            # Deprecated: we'll remove output actions altogether at some point
            if is_env and t.output is not None and len(t.output) > 0:
                result += " # " + ', '.join(map(remove_paren, t.output))
            return result + ']'

        valuations = [fmt_valuation(v) for v in self.valuation]
        other_states = ", ".join([
            state_to_str(s) for s in self.states if s != self.initial_state])
        INDENT = " " * 16
        CN = ",\n" + INDENT
        SN = ";\n" + INDENT
        spec = f"""
            SPECIFICATION {{
              {spec}
            }}
        """ if spec is not None else ""

        prog = f"""\
        program {self.name} {{
            STATES {{
                {state_to_str(self.initial_state)}: init, {other_states}
            }}
            ENVIRONMENT EVENTS {{
                {', '.join(str(e) for e in self.env_events)}
            }}
            CONTROLLER EVENTS {{
                {', '.join(str(e) for e in self.con_events)}
            }}
            PROGRAM EVENTS {{
                {', '.join(str(e) for e in self.out_events)}
            }}
            VALUATION {{
                {SN.join(valuations)}{';' if valuations else ''}
            }}
            TRANSITIONS {{
                {CN.join(tr_to_str(t, False) for t in self.transitions)}
            }}

            {spec}
        }}
        """
        return dedent(prog)

    def to_dot(self):
        dot = Digraph(name=self.name,
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"), ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "rectangle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        to_str = lambda x: ", ".join([str(v) for v in list(x)]) if not isinstance(x, str) and hasattr(x,
                                                                                                      "__iter__") else str(
            x)

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            dot.node(to_str(s))

        dot.edge("init", to_str(self.initial_state), style="solid")

        for t in self.transitions:

            label = str(t.condition)
            if t.action is not None and len(t.action) > 0:
                label = label + " $ " + ', '.join(map(str, t.action))
            if t.output is not None and len(t.output) > 0:
                label = label + " >> " + ', '.join(map(str, t.output))
            dot.edge(to_str(t.src), to_str(t.tgt), label)

        # for t in self.con_transitions:
        #     label = str(t.condition)
        #     if len(t.action) > 0:
        #         label = label + " $ " + ', '.join(map(str, t.action))
        #     dot.edge(to_str(t.src), to_str(t.tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self):
        real_acts = []
        guards = []
        acts = []
        dualise = config.Config.getConfig().dual
        for transition in self.transitions:
            if dualise:
                cond = massage_ltl_for_dual(transition.condition, self.env_events, False)
                cond = str(cond.to_nuxmv()).replace("X(", "next(")
            else:
                cond = str(transition.condition.to_nuxmv())
            guard = "turn = cs & " + str(transition.src) + " & " \
                    + str(cond)

            act = "next(" + str(transition.tgt) + ")" \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(transition.action)]) \
                  + "".join([" & next(" + str(assignment) + ")" for assignment in
                             transition.output]) \
                  + "".join([" & !next(" + str(event) + ")" for event in self.out_events
                             if event not in transition.output]) \
                  + "".join([" & !next(" + st + ")" for st in self.states
                             if st != transition.tgt])
            guards.append(guard)
            acts.append(act)
            real_acts.append((transition.action, transition.output, transition.tgt))

        real_acts.append(([], [], None)) # for the stutter transition

        define = []
        guard_and_act = []
        guard_ids = []

        i = 0
        while i < len(guards):
            define += ["guard_" + str(i) + " := " + guards[i]]
            define += ["act_" + str(i) + " := " + acts[i]]
            guard_ids.append("guard_" + str(i))
            guard_and_act.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            i += 1

        identity = []
        for typed_val in self.valuation:
            identity.append("next(" + str(typed_val.name) + ") = " + str(typed_val.name))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["!next(" + str(event) + ")" for event in self.out_events]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no program events
        guards.append("!(" + " | ".join(guard_ids) + ")")
        acts.append("identity_" + self.name)
        define += ["guard_" + str(len(guards) - 1) + " := " + guards[len(guards) - 1]]
        define += ["act_" + str(len(guards) - 1) + " := " + acts[len(guards) - 1]]

        guard_and_act.append("(guard_" + str(len(guards) - 1) + " & " + "act_" + str(len(guards) - 1) + ")")

        transitions = guard_and_act

        vars = ["turn : {prog, cs}"]
        vars += [str(st) + " : boolean" for st in self.bin_state_vars]

        for typed_val in self.valuation:
            if typed_val.type.startswith("bool"):
                vars.append(str(typed_val.name) + " : " + "boolean")
                vars.append(str(typed_val.name) + "_prev : " + "boolean")
            else:
                vars.append(str(typed_val.name) + " : " + "integer")
                vars.append(str(typed_val.name) + "_prev : " + "integer")

        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.out_events]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [str(val.name) + " = " + str(val.value.to_nuxmv()) for val in self.valuation if not isinstance(val.value, NonDeterministic)]
        init += [str(val.name) + "_prev" + " = " + str(val.value.to_nuxmv()) for val in self.valuation if not isinstance(val.value, NonDeterministic)]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        update_prevs = "(turn = cs)" + " & " + " & ".join(["next(" + str(var.name) + "_prev) = " + str(var.name) for var in self.valuation])
        maintain_prevs = "!(turn = cs)" + " & " + " & ".join(["next(" + str(var.name) + "_prev) = " + str(var.name)  + "_prev" for var in self.valuation])
        prev_logic = "((" + update_prevs + ") | (" + maintain_prevs + "))"
        trans += [prev_logic]

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [str(val.name) + " >= 0" for val in self.valuation if (val.type == "nat" or val.type == "natural")]
        invar.extend([str(val.name) + "_prev" + " >= 0" for val in self.valuation if (val.type == "nat" or val.type == "natural")])

        return NuXmvModel(self.name, vars, define, init, invar, trans)


    def to_nuXmv_with_turns_for_con_verif(self):
        real_acts = []
        guards = []
        acts = []
        for transition in self.transitions:
            cond = str(transition.condition.to_nuxmv())
            guard = str(transition.src) + " & " \
                    + str(cond)

            act = "next(" + str(transition.tgt) + ")" \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(transition.action)]) \
                  + "".join([" & next(" + str(assignment) + ")" for assignment in
                             transition.output]) \
                  + "".join([" & !next(" + str(event) + ")" for event in self.out_events
                             if event not in transition.output]) \
                  + "".join([" & !next(" + st + ")" for st in self.states
                             if st != transition.tgt])
            guards.append(guard)
            acts.append(act)
            real_acts.append((transition.action, transition.output, transition.tgt))

        real_acts.append(([], [], None)) # for the stutter transition

        define = []
        guard_and_act = []
        guard_ids = []

        i = 0
        while i < len(guards):
            define += ["guard_" + str(i) + " := " + guards[i]]
            define += ["act_" + str(i) + " := " + acts[i]]
            guard_ids.append("guard_" + str(i))
            guard_and_act.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            i += 1

        identity = []
        for typed_val in self.valuation:
            identity.append("next(" + str(typed_val.name) + ") = " + str(typed_val.name))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["!next(" + str(event) + ")" for event in self.out_events]

        identity_macro_name = "identity_" + self.name
        define += [identity_macro_name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no program events
        guards.append("!(" + " | ".join(guard_ids) + ")")
        acts.append(identity_macro_name)
        define += ["guard_" + str(len(guards) - 1) + " := " + guards[len(guards) - 1]]
        define += ["act_" + str(len(guards) - 1) + " := " + acts[len(guards) - 1]]

        guard_and_act.append("(guard_" + str(len(guards) - 1) + " & " + "act_" + str(len(guards) - 1) + ")")

        transitions = guard_and_act

        vars = ["turn : {prog, cs}"]
        vars += [str(st) + " : boolean" for st in self.bin_state_vars]

        prev_logic = []

        for typed_val in self.valuation:
            if typed_val.type.startswith("bool"):
                vars.append(str(typed_val.name) + " : " + "boolean")
                vars.append(str(typed_val.name) + "_prev : " + "boolean")
            else:
                vars.append(str(typed_val.name) + " : " + "integer")
                vars.append(str(typed_val.name) + "_prev : " + "integer")

            prev_logic += ["next(" + str(typed_val.name) + "_prev) = " + str(typed_val.name)]

        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.out_events]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [str(val.name) + " = " + str(val.value.to_nuxmv()) for val in self.valuation if not isinstance(val.value, NonDeterministic)]
        init += [str(val.name) + "_prev" + " = " + str(val.value.to_nuxmv()) for val in self.valuation if not isinstance(val.value, NonDeterministic)]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        trans += prev_logic

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [str(val.name) + " >= 0" for val in self.valuation if (val.type == "nat" or val.type == "natural")]
        invar.extend([str(val.name) + "_prev" + " >= 0" for val in self.valuation if (val.type == "nat" or val.type == "natural")])

        return NuXmvModel(self.name, vars, define, init, invar, trans)

    def complete_transitions(self):
        complete_trans = []

        reachable_states = set(
            [s for t in self.transitions for s in [t.tgt, t.src]] + [self.initial_state])

        for s in reachable_states:
            from_s = [t for t in self.transitions if t.src == s]
            stutter_from_s = stutter_transition(self, s, True)
            if stutter_from_s != None:
                from_s += [stutter_from_s]
            complete_trans += from_s

        unsat_trans = [t for t in self.transitions if not sat(t.condition, self.symbol_table)]
        if len(unsat_trans) > 0:
            raise Exception("There are some unsat transitions: " + ",\n".join([str(t) for t in unsat_trans]))
        return complete_trans

    def complete_transitions_stutter_explicit(self):
        complete_trans = []

        reachable_states = set(
            [s for t in self.transitions for s in [t.tgt, t.src]] + [self.initial_state])
        stutter_trans_candidates = []
        for s in reachable_states:
            from_s = [t.complete_outputs(self.out_events) for t in self.transitions if t.src == s]
            stutter_from_s = stutter_transition(self, s, True)
            if stutter_from_s != None:
                stutter_trans_candidates += [stutter_from_s.complete_outputs(self.out_events)]
            complete_trans += from_s

        stutter_trans = stutter_trans_candidates
        # stutter_trans_con = []
        # for stutter_t in stutter_trans_candidates:
        #     if any(t for t in complete_con + stutter_trans_con_candidates if t.tgt == stutter_t.src):
        #         complete_env += [stutter_t]
        #         stutter_trans_env += [stutter_t]

        return complete_trans, stutter_trans

    def complete_action_set(self, actions: [BiOp]):
        non_updated_vars = [tv.name for tv in self.valuation if tv.name not in [str(act.left) for act in actions]]
        return actions + [BiOp(Variable(var), ":=", Variable(var)) for var in non_updated_vars]

    def __str__(self):
        return str(self.to_dot())


def combine_programs(programs: [Program]):
    if len(programs) == 0:
        raise Exception("Cannot combine empty list of programs")
    if len(programs) == 1:
        return programs[0]
    return combine_programs([combine_two_programs(programs[0], programs[1])] + programs[2:])

def combine_two_programs(program_A : Program, program_B : Program):
    valuation = list(set(program_A.valuation + program_B.valuation))
    states = []
    orig_A_to_new = {st_A : [] for st_A in program_A.states}
    orig_B_to_new = {st_B : [] for st_B in program_B.states}
    for st_A in program_A.states:
        for st_B in program_B.states:
            states.append(st_A + "_" + st_B)
            orig_A_to_new[st_A] += [st_A + "_" + st_B]
            orig_B_to_new[st_B] += [st_A + "_" + st_B]
    initial_state = program_A.initial_state + "_" + program_B.initial_state
    env_events = program_A.env_events + program_B.env_events
    con_events = program_A.con_events + program_B.con_events
    out_events = program_A.out_events + program_B.out_events

    new_env_transitions = []
    new_con_transitions = []
    for t_A in program_A.transitions:
        for new_st in orig_A_to_new[t_A.src]:
            # A executes first
            new_src = new_st
            new_tgt = new_st.replace(t_A.src + "_", t_A.tgt + "_")
            guard = t_A.condition
            action = t_A.action
            output = t_A.output
            A_first_t = Transition(new_src, guard, action, output,new_tgt)

            new_env_transitions += [A_first_t]

    for t_B in program_B.transitions:
        for new_st in orig_A_to_new[t_B.src]:
            # B executes first
            new_src = new_st
            new_tgt = new_st.replace("_" + t_B.src, "_" + t_B.tgt)
            guard = t_B.condition
            action = t_B.action
            output = t_B.output

            B_first_t = Transition(new_src, guard, action, output,new_tgt)
            new_env_transitions += [B_first_t]


    for t_A in program_A.con_transitions:
        for new_st in orig_A_to_new[t_A.src]:
            # A executes first
            new_src = new_st
            new_tgt = new_st.replace(t_A.src + "_", t_A.tgt + "_")
            guard = t_A.condition
            action = t_A.action
            output = t_A.output
            A_first_t = Transition(new_src, guard, action, output,new_tgt)

            new_con_transitions += [A_first_t]

    for t_B in program_B.con_transitions:
        for new_st in orig_A_to_new[t_B.src]:
            # B executes first
            new_src = new_st
            new_tgt = new_st.replace("_" + t_B.src, "_" + t_B.tgt)
            guard = t_B.condition
            action = t_B.action
            output = t_B.output

            B_first_t = Transition(new_src, guard, action, output,new_tgt)
            new_con_transitions += [B_first_t]

    return Program(program_A.name + "_" + program_B.name, states, initial_state, valuation, new_env_transitions, new_con_transitions, env_events, con_events, out_events)
