import logging
from multiprocessing import Pool
from textwrap import dedent
from typing import Set

from graphviz import Digraph

import config
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from programs.transition import Transition
from prop_lang.util import reset_caches as prop_lang_util_reset_caches
from programs.util import (
    reset_caches,
    stutter_transition,
    symbol_table_from_program,
    is_deterministic,
    binary_rep_states,
    add_prev_suffix,
)
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import (
    Type,
    Number,
    is_finite,
    BaseNumberTypes,
    BOOLEAN,
    countable_number_types,
    NATURAL,
)
from prop_lang.update import Update
from prop_lang.util import (
    disjunct_formula_set,
    neg,
    true,
    sat,
    type_constraints_acts,
    implies,
    is_tautology,
    sat_parallel,
    mutually_exclusive_rules,
    atomic_predicates,
    simplify_formula_with_math_wo_type_constraints,
    conjunct,
    massage_ltl_for_dual,
    conjunct_formula_set,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


class Program:
    def __init__(
        self,
        name,
        sts,
        init_st,
        init_values: list[tuple[str, Type, Atom]],
        transitions: list[Transition],
        env_events: list[Variable],
        con_events: list[Variable],
        preprocess=True,
        is_determ=None,
    ):
        config.Config.getConfig().cache_smt = False
        reset_caches()

        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.constants = {}

        if config.Config.getConfig().dual:
            self.env_events = con_events
            self.con_events = env_events
        else:
            self.env_events = env_events
            self.con_events = con_events
        self.out_events = []

        self.symbol_table, self.init_var_values = symbol_table_from_program(
            self, init_values
        )
        self.local_vars: list[Variable] = [Variable(n) for n, _, _ in init_values]

        self.transitions = transitions

        if len(self.transitions) == 0:
            self.transitions = [Transition(s, true(), [], [], s) for s in self.states]

        all_vars = self.local_vars
        self.transitions = [
            self.add_type_constraints_to_guards(t)
            .complete_outputs(self.out_events)
            .complete_action_set(all_vars)
            for t in self.transitions
        ]

        if preprocess:
            logging.info("Processing program.")
            print("Processing program.")
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
                logging.info(
                    "Removed transitions with unsat transitions: "
                    + ",\n".join(map(str, unsat_trans))
                )

        otherwise = [t for t in self.transitions if str(t.condition) == "otherwise"]
        if len(otherwise) > 1:
            raise Exception("Too many environment otherwise transitions")
        elif len(otherwise) == 1:
            otherwise_trans = otherwise[0]
            condition = neg(
                disjunct_formula_set(
                    [
                        t.condition
                        for t in transitions
                        if t.src == otherwise_trans.src and t != otherwise_trans
                    ]
                )
            )
            if sat(condition, self.symbol_table):
                concrete_trans = Transition(
                    otherwise_trans.src,
                    condition,
                    otherwise_trans.action,
                    otherwise_trans.output,
                    otherwise_trans.tgt,
                )
                self.transitions.append(concrete_trans)
            self.transitions.remove(otherwise_trans)

        (
            self.orig_ts,
            self.stutter_ts,
        ) = self.complete_transitions_stutter_explicit()
        self.transitions = self.orig_ts + self.stutter_ts
        # TODO this can take a long time, see concurrent-safety-response
        self.state_to_trans = {}
        for t in self.transitions:
            if t.src in self.state_to_trans.keys():
                self.state_to_trans[t.src].append(t)
            else:
                self.state_to_trans[t.src] = [t]

        self.deterministic = None
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

        # if not config.Config.getConfig().no_binary_enc:
        self.bin_state_vars, self.states_binary_map = binary_rep_states(self.states)
        self.bin_to_orig_state_map = {st: k for k, st in self.states_binary_map.items()}
        self.states_binary_map |= {
            Variable(st): bin_st for st, bin_st in self.states_binary_map.items()
        }
        self.symbol_table.update({str(b): BOOLEAN for b in self.bin_state_vars})
        # TODO: the below is wrong, if incorporated needs to be corrected so that states are mutually exclusive
        # else:
        #     self.bin_state_vars = list(self.states)
        #     self.bin_to_orig_state_map = {st: st for st in self.states}
        #     self.states_binary_map = {(st): Variable(st) for st in self.states}

        self.project_out_constants()
        # note, we do not need to add natural type constraints to transitions after this call here,
        # since we are refining integers to naturals only when every transition already
        # preserves the natural constraint
        while self.refine_var_types():
            prop_lang_util_reset_caches()
            reset_caches()
            # TODO: should we adding type constraints in transitions here again?
            pass

        # doing this after refining var types; otherwise the wrong type constraints will be added to smt calls
        config.Config.getConfig().cache_smt = True

    def refine_var_types(self):
        from prop_lang.types.types import NATURAL

        new_symbol_table = {}

        # Create valuation from init_var_values
        current_vals = [
            BiOp(Variable(name), "=", val) for name, val in self.init_var_values.items()
        ]
        current_valuation = (
            conjunct_formula_set(current_vals) if current_vals else true()
        )

        for n, type_obj in self.symbol_table.items():
            if isinstance(type_obj, Number) and not str(n).endswith("_prev"):
                v = Variable(n)
                if not (
                    isinstance(type_obj, Number)
                    and type_obj.number_type == BaseNumberTypes.integer
                ):
                    continue
                nat_pred = BiOp(v, ">=", Value("0"))

                if not is_tautology(
                    implies(current_valuation, nat_pred),
                    self.symbol_table,
                ):
                    continue

                exit = False
                prev_nat = add_prev_suffix(nat_pred)

                for t in self.transitions:
                    if not is_tautology(
                        implies(conjunct(prev_nat, t.formula()), nat_pred),
                        self.symbol_table,
                    ):
                        exit = True
                        break

                if not exit:
                    print("turned " + n + " into a natural")
                    new_symbol_table[n] = NATURAL
                    new_symbol_table[n + "_prev"] = NATURAL
                    new_symbol_table[n + "_prev_prev"] = NATURAL

        self.symbol_table.update(new_symbol_table)
        return len(new_symbol_table) > 0

    def project_out_constants(self):
        # Early check to see if any variables are constant
        constant_vars = set()
        for var_name in self.init_var_values.keys():
            var_obj = Variable(var_name)
            identity_action = Update(var_obj, var_obj)
            if all(identity_action in t.action for t in self.transitions):
                constant_vars.add(var_name)

        if not constant_vars:
            return

        # Build projection mapping and new valuation
        vars_to_project_out = {}
        new_init_var_values = {}

        for var_name, var_value in self.init_var_values.items():
            if var_name in constant_vars:
                vars_to_project_out[Variable(var_name)] = var_value
            else:
                new_init_var_values[var_name] = var_value

        # Process transitions
        for t in self.transitions:
            # Filter actions and replace variables
            t.action = [
                Update(
                    a.left,
                    a.right.replace_vars(lambda x: vars_to_project_out.get(x, x)),
                )
                for a in t.action
                if a.left not in vars_to_project_out
            ]

            # Only process condition if it contains variables to project out
            preds_in_cond = atomic_predicates(t.condition)
            preds_to_replace = {}

            for p in preds_in_cond:
                pred_vars = p.variablesin()
                if not vars_to_project_out.keys().isdisjoint(pred_vars):
                    preds_to_replace[p] = (
                        simplify_formula_with_math_wo_type_constraints(
                            p.replace_formulas(vars_to_project_out), self.symbol_table
                        )
                    )

            if preds_to_replace:
                t.condition = t.condition.replace_formulas(preds_to_replace)

        # Update symbol table and data structures
        var_names_to_delete = [v.name for v in vars_to_project_out.keys()]
        for var_name in var_names_to_delete:
            self.constants[Variable(var_name)] = self.init_var_values[var_name]
            del self.symbol_table[var_name]
            del self.symbol_table[var_name + "_prev"]
            del self.symbol_table[var_name + "_prev_prev"]

        self.init_var_values = new_init_var_values
        self.local_vars = [Variable(name) for name in new_init_var_values.keys()]

    def add_type_constraints_to_guards(self, transition: Transition):
        constraints = type_constraints_acts(transition, self.symbol_table)
        if not is_tautology(
            implies(transition.condition, constraints), self.symbol_table
        ):
            return transition.add_condition(constraints)
        else:
            return transition

    def is_finite_state(self):
        return all(is_finite(type_obj) for type_obj in self.symbol_table.values())

    def to_prog(self, spec=None):
        def state_to_str(x):
            if not isinstance(x, str) and hasattr(x, "__iter__"):
                return ", ".join(str(v) for v in list(x))
            return str(x)

        def fmt_valuation(name, value, var_type):
            return f"{name} : {var_type} := {str(value).lower()}"

        def tr_to_str(t, is_env):
            def remove_paren(s):
                s1 = str(s)
                return s1[1:-1] if s1.startswith("(") else s1

            result = f"{state_to_str(t.src)} -> {state_to_str(t.tgt)} [{remove_paren(t.condition)}"
            if t.action is not None and len(t.action) > 0:
                result += " $ " + "; ".join(map(remove_paren, t.action))
            if is_env and t.output is not None and len(t.output) > 0:
                result += " # " + ", ".join(map(remove_paren, t.output))
            return result + "]"

        # Create valuations from init_var_values and symbol_table
        valuations = [
            fmt_valuation(name, value, self.symbol_table[name])
            for name, value in self.init_var_values.items()
        ]

        other_states = ", ".join(
            [state_to_str(s) for s in self.states if s != self.initial_state]
        )
        INDENT = " " * 16
        CN = ",\n" + INDENT
        SN = ";\n" + INDENT
        spec = (
            f"""
            SPECIFICATION {{
              {spec}
            }}
        """
            if spec is not None
            else ""
        )

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
        dot = Digraph(
            name=self.name,
            graph_attr=[
                ("overlap", "scalexy"),
                ("splines", "true"),
                ("ranksep", "0.8"),
                ("nodesep", "0.5"),
            ],
            node_attr=[("shape", "rectangle")],
            edge_attr=[("fontname", "mono")],
            engine="dot",
            format="svg",
        )

        to_str = lambda x: (
            ", ".join([str(v) for v in list(x)])
            if not isinstance(x, str) and hasattr(x, "__iter__")
            else str(x)
        )

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            dot.node(to_str(s))

        dot.edge("init", to_str(self.initial_state), style="solid")

        for t in self.transitions:

            label = str(t.condition)
            if t.action is not None and len(t.action) > 0:
                label = label + " $ " + ", ".join(map(str, t.action))
            if t.output is not None and len(t.output) > 0:
                label = label + " >> " + ", ".join(map(str, t.output))
            dot.edge(to_str(t.src), to_str(t.tgt), label)

        # for t in self.con_transitions:
        #     label = str(t.condition)
        #     if len(t.action) > 0:
        #         label = label + " $ " + ', '.join(map(str, t.action))
        #     dot.edge(to_str(t.src), to_str(t.tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self):
        guards = []
        acts = []
        dualise = config.Config.getConfig().dual
        for transition in self.transitions:
            if dualise:
                cond = massage_ltl_for_dual(
                    transition.condition, self.env_events, False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            else:
                cond = transition.condition.to_nuxmv()
            guard = "turn = cs & " + str(transition.src) + " & " + cond

            act = (
                "next("
                + str(transition.tgt)
                + ") &"
                + conjunct_formula_set(
                    self.complete_action_set(transition.action)
                ).to_nuxmv()
                # + "".join(
                #     [
                #         " & next(" + str(assignment) + ")"
                #         for assignment in transition.output
                #     ]
                # )
                # + "".join(
                #     [
                #         " & !next(" + str(event) + ")"
                #         for event in self.out_events
                #         if event not in transition.output
                #     ]
                # )
                + "".join(
                    [
                        " & !next(" + st + ")"
                        for st in self.states
                        if st != transition.tgt
                    ]
                )
            )
            guards.append(guard)
            acts.append(act)

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
        for var in self.init_var_values.keys():
            identity.append("next(" + str(var) + ") = " + str(var))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["!next(" + str(event) + ")" for event in self.out_events]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no program events
        guards.append("!(" + " | ".join(guard_ids) + ")")
        acts.append("identity_" + self.name)
        define += ["guard_" + str(len(guards) - 1) + " := " + guards[len(guards) - 1]]
        define += ["act_" + str(len(guards) - 1) + " := " + acts[len(guards) - 1]]

        guard_and_act.append(
            "(guard_"
            + str(len(guards) - 1)
            + " & "
            + "act_"
            + str(len(guards) - 1)
            + ")"
        )

        transitions = guard_and_act

        vars = ["turn : {prog, cs}"]
        vars += sorted([s + " : boolean" for s in self.states])

        for var, _ in self.init_var_values.items():
            var_type = self.symbol_table[var]
            if var_type == BOOLEAN:
                vars.append(var + " : " + "boolean")
                vars.append(var + "_prev : " + "boolean")
            elif (
                isinstance(var_type, Number)
                and var_type.number_type in countable_number_types
            ):
                vars.append(var + " : " + "integer")
                vars.append(var + "_prev : " + "integer")
            else:
                raise Exception("Unsupported type for variable: " + str(var_type))

        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.out_events]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [
            str(var) + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        init += [
            str(var) + "_prev" + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        update_prevs = "(turn = cs)" + (
            " & "
            + " & ".join(
                [
                    "next(" + str(var) + "_prev) = " + str(var)
                    for var in self.init_var_values.keys()
                ]
            )
            if len(self.init_var_values) > 0
            else ""
        )
        maintain_prevs = "!(turn = cs)" + (
            " & "
            + " & ".join(
                [
                    "next(" + str(var) + "_prev) = " + str(var) + "_prev"
                    for var in self.init_var_values.keys()
                ]
            )
            if len(self.init_var_values) > 0
            else ""
        )
        prev_logic = "((" + update_prevs + ") | (" + maintain_prevs + "))"
        trans += [prev_logic]

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [
            str(var) + " >= 0"
            for var in self.init_var_values.keys()
            if self.symbol_table[var] == NATURAL
        ]
        invar.extend(
            [
                str(var) + "_prev" + " >= 0"
                for var in self.init_var_values.keys()
                if self.symbol_table[var] == NATURAL
            ]
        )

        return NuXmvModel(self.name, vars, define, init, invar, trans)

    def to_nuXmv_with_turns_for_con_verif(self):
        real_acts = []
        guards = []
        acts = []
        dualise = config.Config.getConfig().dual
        for transition in self.transitions:
            if dualise:
                cond = massage_ltl_for_dual(
                    transition.condition, self.env_events, False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            else:
                cond = transition.condition.to_nuxmv()
            guard = str(transition.src) + " & " + cond

            act = (
                "next("
                + str(transition.tgt)
                + ")"
                + "".join(
                    [
                        " & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv())
                        for act in self.complete_action_set(transition.action)
                    ]
                )
                + "".join(
                    [
                        " & next(" + str(assignment) + ")"
                        for assignment in transition.output
                    ]
                )
                + "".join(
                    [
                        " & !next(" + str(event) + ")"
                        for event in self.out_events
                        if event not in transition.output
                    ]
                )
                + "".join(
                    [
                        " & !next(" + st + ")"
                        for st in self.states
                        if st != transition.tgt
                    ]
                )
            )
            guards.append(guard)
            acts.append(act)
            real_acts.append((transition.action, transition.output, transition.tgt))

        real_acts.append(([], [], None))  # for the stutter transition

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
        for var in self.init_var_values.keys():
            identity.append("next(" + str(var) + ") = " + str(var))
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

        guard_and_act.append(
            "(guard_"
            + str(len(guards) - 1)
            + " & "
            + "act_"
            + str(len(guards) - 1)
            + ")"
        )

        transitions = guard_and_act

        vars = ["turn : {prog, cs}"]
        vars += sorted([s + " : boolean" for s in self.states])

        prev_logic = []

        for var, _ in self.init_var_values.items():
            var_type = self.symbol_table[var]
            if var_type == BOOLEAN:
                vars.append(var + " : " + "boolean")
                vars.append(var + "_prev : " + "boolean")
            elif (
                isinstance(var_type, Number)
                and var_type.number_type in countable_number_types
            ):
                vars.append(var + " : " + "integer")
                vars.append(var + "_prev : " + "integer")
            else:
                raise Exception("Unsupported type for variable: " + str(var_type))

            prev_logic += ["next(" + str(var) + "_prev) = " + str(var)]

        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.out_events]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [
            var + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        init += [
            var + "_prev" + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        trans += prev_logic

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [
            str(var) + " >= 0"
            for var in self.init_var_values.keys()
            if self.symbol_table[var] == NATURAL
        ]
        invar.extend(
            [
                str(var) + "_prev" + " >= 0"
                for var in self.init_var_values.keys()
                if self.symbol_table[var] == NATURAL
            ]
        )

        return NuXmvModel(self.name, vars, define, init, invar, trans)

    def complete_transitions(self):
        complete_trans = []

        reachable_states = set(
            [s for t in self.transitions for s in [t.tgt, t.src]] + [self.initial_state]
        )

        for s in reachable_states:
            from_s = [t for t in self.transitions if t.src == s]
            stutter_from_s = stutter_transition(self, s, True)
            if stutter_from_s != None:
                from_s += [stutter_from_s]
            complete_trans += from_s

        unsat_trans = [
            t for t in self.transitions if not sat(t.condition, self.symbol_table)
        ]
        if len(unsat_trans) > 0:
            raise Exception(
                "There are some unsat transitions: "
                + ",\n".join([str(t) for t in unsat_trans])
            )
        return complete_trans

    def complete_transitions_stutter_explicit(self):
        complete_trans = []

        reachable_states = set(
            [s for t in self.transitions for s in [t.tgt, t.src]] + [self.initial_state]
        )
        stutter_trans_candidates = []
        for s in reachable_states:
            from_s = [
                t.complete_outputs(self.out_events)
                for t in self.transitions
                if t.src == s
            ]
            stutter_from_s = stutter_transition(self, s, True)
            if stutter_from_s != None:
                stutter_trans_candidates += [
                    stutter_from_s.complete_outputs(self.out_events)
                ]
            complete_trans += from_s

        stutter_trans = stutter_trans_candidates
        # stutter_trans_con = []
        # for stutter_t in stutter_trans_candidates:
        #     if any(t for t in complete_con + stutter_trans_con_candidates if t.tgt == stutter_t.src):
        #         complete_env += [stutter_t]
        #         stutter_trans_env += [stutter_t]

        return complete_trans, stutter_trans

    def complete_action_set(self, actions: list[BiOp]):
        non_updated_vars = [
            var_name
            for var_name in self.init_var_values.keys()
            if var_name not in [str(act.left) for act in actions]
        ]
        return actions + [
            Update(Variable(var), Variable(var)) for var in non_updated_vars
        ]

    def __str__(self):
        return str(self.to_dot())
