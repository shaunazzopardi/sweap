import itertools
import math
import logging
from collections import deque
from multiprocessing import Pool
from textwrap import dedent
from typing import Set, Union

from graphviz import Digraph
from analysis.sat_context import IncrementalSatContext, NonIncrementalSatContext
import config
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from programs.dfa import (
    program_sccs,
    reachable_states,
    simplify_with_location_constants,
)
from programs.transition import Transition
from prop_lang.formula import Formula
from prop_lang.util import (
    reset_caches as prop_lang_util_reset_caches,
    type_constraint,
)
from programs.util import (
    reset_caches,
    stutter_transition,
    symbol_table_from_program,
    is_deterministic,
    binary_rep_states,
    add_prev_suffix,
    transition_formula,
    issy_transition_formula,
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
        init_values: list[Union[tuple[str, Type], tuple[str, Type, Atom]]],
        transitions: list[Transition],
        env_events: list[tuple[Variable, Type]],
        con_events: list[tuple[Variable, Type]],
        preprocess=True,
        is_determ=None,
        emit_state_binary_map=True,
    ):
        config.Config.getConfig().cache_smt = False
        reset_caches()

        if not name:
            raise Exception("Program must have a name.")
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.constants = {}
        self.binary_rep_tables: dict[str, str] = {}

        inputs = [v for v, _ in env_events]
        outputs = [v for v, _ in con_events]

        # TODO update to Types not str
        self.inp_out_puts = inputs + outputs
        self.num_in_out = [v for v, t in env_events + con_events if not t == BOOLEAN]
        self.bool_in_out = [v for v in inputs + outputs if v not in self.num_in_out]

        if config.Config.getConfig().dual:
            self.env_events = con_events
            self.con_events = env_events
            self.inputs = outputs
            self.outputs = inputs
        else:
            self.env_events = env_events
            self.con_events = con_events
            self.inputs = inputs
            self.outputs = outputs

        # check that non-boolean events only in env events
        for ev, t in con_events:
            if not t == BOOLEAN:
                raise Exception(
                    "Only environment events can have non-boolean variables: "
                    + str(ev)
                    + ": "
                    + str(t)
                )

        self.out_events = []

        self.symbol_table, self.init_var_values, self.unset_init_vars = (
            symbol_table_from_program(self, init_values)
        )
        self.local_vars_str: list[str] = [v[0] for v in init_values]
        self.local_vars: list[Variable] = [Variable(v) for v in self.local_vars_str]

        self.transitions = transitions

        if len(self.transitions) == 0:
            self.transitions = [Transition(s, true(), [], [], s) for s in self.states]

        all_vars = self.local_vars
        self.transitions = [
            t.complete_outputs(self.out_events).complete_action_set(all_vars)
            for t in self.transitions
        ]

        init_type_constraints = []
        for v, t in self.symbol_table.items():
            if isinstance(t, Number) and t.interval:
                init_type_constraints.append(
                    type_constraint(Variable(v), self.symbol_table)
                )

        self.init_type_constraints = conjunct_formula_set(init_type_constraints)

        self.deterministic = is_determ

        if preprocess or config.Config.getConfig().debug:
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

        if (
            preprocess and self.deterministic is None
        ) or config.Config.getConfig().debug:
            self.deterministic = is_deterministic(self)

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

        if config.Config.getConfig().opt_location_constant_simplify:
            simplified, removed_unsat = simplify_with_location_constants(self)
            if simplified > 0 or removed_unsat > 0:
                logging.info(
                    "Location-constant simplification: simplified "
                    + str(simplified)
                    + " transitions, removed "
                    + str(removed_unsat)
                    + " unsat transitions."
                )

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

        reachable_statess, self.reachable_from = reachable_states(self)
        if len(reachable_statess) != len(self.states):
            print(
                "Removed unreachable states: "
                + ", ".join(map(str, self.states - reachable_statess))
            )
            self.states = reachable_statess
            self.transitions = [t for t in self.transitions if t.src in self.states]
            self.orig_ts = [t for t in self.orig_ts if t.src in self.states]
            self.stutter_ts = [t for t in self.stutter_ts if t.src in self.states]
            self.state_to_trans = {
                k: v for k, v in self.state_to_trans.items() if k in self.states
            }

        # if not config.Config.getConfig().no_binary_enc:
        self.bin_state_vars, self.states_binary_map = binary_rep_states(
            self.states,
            printing=False,
            log=emit_state_binary_map,
            collect_to=self,
        )
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

        self.updates = {u for trans in self.transitions for u in trans.action}
        self.sccs = program_sccs(self)
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

    def register_binary_rep_table(self, label: str, table: str):
        self.binary_rep_tables[label] = table

    def get_binary_rep_tables(self) -> list[str]:
        return list(self.binary_rep_tables.values())

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
            if (
                isinstance(type_obj, Number)
                and not str(n).endswith("_prev")
                and n not in self.inputs
                and n not in self.outputs
            ):
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
        for v in vars_to_project_out.keys():
            self.local_vars.remove(v)
            self.local_vars_str.remove(str(v))

    def add_type_constraints_to_guards(self, transition: Transition):
        constraints = type_constraints_acts(transition, self.symbol_table)
        # constraints += list(type_constraints(transition.condition, self.symbol_table))
        ts = []
        if len(constraints) == 0:
            ts.append(transition)
        else:
            # if not is_tautology(
            #     implies(transition.condition, constraints), self.symbol_table
            # ):
            ts.append(transition.add_condition(conjunct_formula_set(constraints)))
        # else:
        #     return transition

        return ts

    def is_finite_state(self):
        return all(is_finite(type_obj) for type_obj in self.symbol_table.values())

    def to_prog(self, spec=None):
        def state_to_str(x):
            if not isinstance(x, str) and hasattr(x, "__iter__"):
                return ", ".join(str(v) for v in list(x))
            return str(x)

        def fmt_valuation(name, value, var_type):
            return f"{name} : {var_type} := {str(value).lower()}"

        def fmt_valuation_no_init(name, var_type):
            return f"{name} : {var_type}"

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
        ] + [
            fmt_valuation_no_init(name, self.symbol_table[name])
            for name in self.unset_init_vars
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
                {', '.join(f"{e} : {t}" for e, t in self.env_events)}
            }}
            CONTROLLER EVENTS {{
                {', '.join(f"{e} : {t}" for e, t in self.con_events)}
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

    def to_issy(self, spec):
        vars = ""

        def sweap_type_to_issy(t):
            if t == BOOLEAN:
                return "bool"
            elif isinstance(t, Number):
                return "int"
            else:
                raise Exception("Unsupported type for ISSY: " + str(t))

        for i, t in self.env_events:
            vars += f"input {sweap_type_to_issy(t)} {i}\n"
        for i, t in self.con_events:
            vars += f"state {sweap_type_to_issy(t)} {i}\n"
        for i in self.local_vars:
            vars += f"state {sweap_type_to_issy(self.symbol_table[str(i)])} {i}\n"
        states_in_spec = {
            str(s) for s in atomic_predicates(spec) if str(s) in self.states
        }
        for s in states_in_spec:
            vars += f"state bool {s}\n"

        game_state = "\t" + "\n\t".join([f"loc {s} 1" for s in self.states])
        transitions = "\t" + "\n\n\t".join(
            map(lambda x: issy_transition_formula(x, states_in_spec), self.transitions)
        )

        game = (
            f"game Safety from {self.initial_state} "
            + "{\n"
            + game_state
            + "\n\n"
            + transitions
            + "\n}"
        )
        assertion = f"assert {str(spec)}"

        init_vals = []
        for v, k in self.init_var_values.items():
            init_vals.append(f"[{v} = {k}]")

        if len(init_vals) > 0:
            assume = "assume " + " && ".join(init_vals)
            objective = assume + "\n\t" + assertion
        else:
            objective = assertion

        if states_in_spec:
            init_assumptions = []
            for s in states_in_spec:
                if s == self.initial_state:
                    init_assumptions.append(f"assume [{self.initial_state}]")
                else:
                    init_assumptions.append(f"assume ![{s}]")
            objective = "\n\t".join(init_assumptions) + "\n\t" + objective

        full = "formula {\n\t" + objective + "\n}\n\n" + vars + "\n" + game
        full.replace(" & ", " && ").replace(" | ", " || ")
        return full

    def to_dot(self):
        dot = Digraph(
            name=self.name + "_dot",
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
        dual2 = config.Config.getConfig().dual2
        for transition in self.transitions:
            if dualise:
                # cond = (
                #     transition.condition.to_nuxmv()
                # )
                cond = massage_ltl_for_dual(
                    transition.condition, [v for v, _ in self.env_events], False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            elif dual2:
                # cond = (
                #     transition.condition.to_nuxmv()
                # )
                cond = massage_ltl_for_dual(
                    transition.condition, self.bool_in_out + self.num_in_out, False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            else:
                cond = transition.condition.to_nuxmv()
            pred_upgrades_cond = conjunct_formula_set(
                transition.pred_upgrades
            ).to_nuxmv()
            guard = (
                "turn = cs & "
                + str(transition.src)
                + " & "
                + cond
                + " & "
                + pred_upgrades_cond
            )

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
        for var in self.local_vars:
            identity.append("next(" + str(var) + ") = " + str(var))
        for var in self.num_in_out:
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

        if dualise or dual2:
            vars = ["turn : {prog, cs, init1}"]
        else:
            vars = ["turn : {prog, cs}"]
        vars += sorted([s + " : boolean" for s in self.states])

        for v in self.local_vars + self.num_in_out:
            var = v.name
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
                vars.append(var + "_prev_prev : " + "integer")
            else:
                raise Exception("Unsupported type for variable: " + str(var_type))

        vars += [str(var) + " : boolean" for var in self.out_events + self.bool_in_out]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [
            str(var) + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        # init += [str(var) + "_prev" + " = " + str(var) for var in self.local_vars]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        locals_plus_inputs = self.local_vars + self.num_in_out
        update_prevs = "(turn = cs)" + (
            " & "
            + " & ".join(
                [
                    "next(" + str(var) + "_prev) = " + str(var)
                    for var in locals_plus_inputs
                ]
            )
            if len(locals_plus_inputs) > 0
            else ""
        )
        maintain_prevs = "!(turn = cs)" + (
            " & "
            + " & ".join(
                [
                    "next(" + str(var) + "_prev) = " + str(var) + "_prev"
                    for var in locals_plus_inputs
                ]
            )
            if len(locals_plus_inputs) > 0
            else ""
        )
        prev_logic = "((" + update_prevs + ") | (" + maintain_prevs + "))"
        trans += [prev_logic]

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]

        all_numeric_vars = map(str, self.local_vars + self.num_in_out)

        invar += [
            str(var) + " >= 0"
            for var in all_numeric_vars
            if self.symbol_table[var] == NATURAL
        ]
        invar.extend(
            [
                var + "_prev" + " >= 0"
                for var in all_numeric_vars
                if self.symbol_table[var] == NATURAL
            ]
        )
        # add interval constraints

        invar.extend(
            [
                var
                + (">= " if n.interval.lower_inclusive else ">")
                + str(n.interval.lower)
                for var in all_numeric_vars
                if isinstance(n := self.symbol_table[var], Number)
                and n.interval
                and n.interval.lower != ""
            ]
        )
        invar.extend(
            [
                var
                + ("<= " if n.interval.upper_inclusive else "<")
                + str(n.interval.upper)
                for var in all_numeric_vars
                if isinstance(n := self.symbol_table[var], Number)
                and n.interval
                and n.interval.upper != ""
            ]
        )

        return NuXmvModel(self.name, vars, define, init, invar, trans)

    def to_nuXmv_with_turns_for_con_verif(
        self,
        include_pred_upgrades: bool = False,
        stutter_when_other_game_in_minigame: bool = False,
    ):
        real_acts = []
        guards = []
        acts = []
        dualise = config.Config.getConfig().dual
        dual2 = config.Config.getConfig().dual2
        for transition in self.transitions:
            if dualise:
                cond = massage_ltl_for_dual(
                    transition.condition, [v for v, _ in self.env_events], False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            elif dual2:
                cond = massage_ltl_for_dual(
                    transition.condition, self.bool_in_out + self.num_in_out, False
                )
                cond = cond.to_nuxmv().replace("X(", "next(")
            else:
                cond = transition.condition.to_nuxmv()
            guard = str(transition.src) + " & " + cond
            if include_pred_upgrades and len(transition.pred_upgrades) > 0:
                pred_upgrades_cond = conjunct_formula_set(
                    transition.pred_upgrades
                ).to_nuxmv()
                guard = guard + " & " + pred_upgrades_cond
            if stutter_when_other_game_in_minigame:
                guard = "(" + guard + ") & !other_game_in_minigame"

            act = (
                "next("
                + str(transition.tgt)
                + ")"
                + "".join(
                    [
                        " & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv())
                        for act in self.complete_action_set(transition.action)
                        if not isinstance(act.right, NonDeterministic)
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
        for var in self.local_vars_str:
            identity.append("next(" + var + ") = " + var)
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))
        if stutter_when_other_game_in_minigame:
            identity.append("next(other_game_in_minigame) = other_game_in_minigame")

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

        vars = sorted([s + " : boolean" for s in self.states])
        if stutter_when_other_game_in_minigame:
            vars.append("other_game_in_minigame : boolean")

        prev_logic = []

        for v in self.local_vars + self.num_in_out:
            var = v.name
            var_type = self.symbol_table[var]
            if var_type == BOOLEAN:
                vars.append(var + " : " + "boolean")
                vars.append(var + "_prev : " + "boolean")
                vars.append(var + "_prev_prev : " + "boolean")
            elif (
                isinstance(var_type, Number)
                and var_type.number_type in countable_number_types
            ):
                vars.append(var + " : " + "integer")
                vars.append(var + "_prev : " + "integer")
                vars.append(var + "_prev_prev : " + "integer")
            else:
                raise Exception("Unsupported type for variable: " + str(var_type))

            prev_logic += ["next(" + str(var) + "_prev) = " + str(var)]
            prev_logic += ["next(" + str(var) + "_prev_prev) = " + str(var + "_prev")]

        vars += [str(var) + " : boolean" for var in self.out_events + self.bool_in_out]

        init = [self.initial_state]
        init += ["!" + st for st in self.states if st != self.initial_state]
        init += [
            var + " = " + str(value.to_nuxmv())
            for var, value in self.init_var_values.items()
            if not isinstance(value, NonDeterministic)
        ]
        if stutter_when_other_game_in_minigame:
            init += ["!other_game_in_minigame"]
        # init += [str(var) + "_prev" + " = " + str(var) for var in self.local_vars]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        trans += prev_logic

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]

        all_numeric_vars = map(str, self.local_vars + self.num_in_out)

        invar += [
            var + " >= 0"
            for var in all_numeric_vars
            if self.symbol_table[var] == NATURAL
        ]
        invar.extend(
            [
                var + "_prev" + " >= 0"
                for var in all_numeric_vars
                if self.symbol_table[var] == NATURAL
            ]
        )

        invar.extend(
            [
                str(var)
                + (">= " if n.interval.lower_inclusive else ">")
                + str(n.interval.lower)
                for var in all_numeric_vars
                if isinstance(n := self.symbol_table[str(var)], Number)
                and n.interval
                and n.interval.lower != ""
            ]
        )

        invar.extend(
            [
                str(var)
                + ("<= " if n.interval.upper_inclusive else "<")
                + str(n.interval.upper)
                for var in all_numeric_vars
                if isinstance(n := self.symbol_table[str(var)], Number)
                and n.interval
                and n.interval.upper != ""
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
            v
            for v in self.local_vars_str
            if v not in [str(act.left) for act in actions]
        ]
        return actions + [Update(var, var) for var in non_updated_vars]

    def __str__(self):
        return str(self.to_dot())


def program_cross_product(
    programs: list[Program], symbol_table, losing_states, lose_var, name=None
):
    # Implement cross product of multiple programs
    new_states_combinations = itertools.product(
        *[list(prog.states) for prog in programs]
    )
    new_initial_state = "_".join(prog.initial_state for prog in programs)
    new_states = set()
    prog_old_to_new_state = {
        i: {Variable(s): set() for s in programs[i].states}
        for i in range(len(programs))
    }

    new_transitions = []
    # TODO: optimise with parallel processing, and ?
    for state_tuple in new_states_combinations:
        possible_transitions = []
        for i, prog in enumerate(programs):
            from_state = state_tuple[i]
            transitions_from_state = prog.state_to_trans[from_state]
            possible_transitions.append(transitions_from_state)
        print("TRAN COMBS: " + str(len(list(itertools.product(*possible_transitions)))))
        for transition_combination in itertools.product(*possible_transitions):
            cond = conjunct_formula_set(
                conjunct(
                    transition_formula(t),
                    conjunct_formula_set([p.prev_rep() for p in t.pred_upgrades]),
                )
                for t in transition_combination
            )
            if (
                "lose" in state_tuple
                or any(
                    i
                    for i in range(len(state_tuple))
                    if state_tuple[i] in losing_states[i]
                )
                or not sat(cond, symbol_table)
            ):
                print("NOT SAT: " + str(cond))
                continue
            combined_src = "_".join(state_tuple)
            new_states.add(combined_src)
            for i in range(len(state_tuple)):
                prog_old_to_new_state[i][Variable(state_tuple[i])].add(
                    Variable(combined_src)
                )
            tgt_tuple = [t.tgt for t in transition_combination]
            if "lose" in tgt_tuple:
                combined_tgt = lose_var
                new_states.add(combined_tgt)
                for i in range(len(tgt_tuple)):
                    prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(
                        Variable(combined_tgt)
                    )
            elif losing := [
                i for i in range(len(tgt_tuple)) if tgt_tuple[i] in losing_states[i]
            ]:
                combined_tgt = lose_var
                new_states.add(combined_tgt)
                for i in losing:
                    prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(lose_var)
            else:
                combined_tgt = "_".join(t.tgt for t in transition_combination)
                new_states.add(combined_tgt)
                for i in range(len(tgt_tuple)):
                    prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(
                        Variable(combined_tgt)
                    )
            combined_condition = conjunct_formula_set(
                [t.condition for t in transition_combination]
            )
            combined_actions = set()
            combined_outputs = []
            for t in transition_combination:
                combined_actions.update(t.action)
                combined_outputs.extend(t.output)

            left_to_u = {}
            # sorting ensures deterministic choice for which update to add to combined condition
            # preferring to keep updates with less variables in case of conflict
            combined_actions = sorted(
                combined_actions, key=lambda x: len(x.variablesin())
            )
            for u in combined_actions:
                if u.left in left_to_u.keys():
                    # conflict, keep deterministic one
                    if not isinstance(u.right, NonDeterministic) and not isinstance(
                        left_to_u[u.left].right, NonDeterministic
                    ):
                        combined_condition = conjunct(
                            combined_condition,
                            BiOp(u.right, "=", left_to_u[u.left].right),
                        )
                    elif not isinstance(u.right, NonDeterministic) and isinstance(
                        left_to_u[u.left].right, NonDeterministic
                    ):
                        left_to_u[u.left] = u
                else:
                    left_to_u[u.left] = u
            combined_actions = set(left_to_u.values())

            new_t = Transition(
                combined_src,
                combined_condition,
                list(combined_actions),
                combined_outputs,
                combined_tgt,
            )
            new_t.pred_upgrades = set(
                itertools.chain.from_iterable(
                    [tt.pred_upgrades for tt in transition_combination]
                )
            )
            if len(new_t.pred_upgrades) > 0:
                print("NEW T WITH PREDS: " + str(new_t))
            new_transitions.append(new_t)

    new_prog = Program(
        name=name if name else "_xprod_".join([prog.name for prog in programs]),
        sts=list(new_states_combinations),
        init_st=new_initial_state,
        init_values=list(
            {
                (var.name, symbol_table[var.name])
                for prog in programs
                for var in prog.local_vars
            }
        ),
        transitions=new_transitions,
        env_events=list({(var, t) for prog in programs for var, t in prog.env_events}),
        con_events=list({(var, t) for prog in programs for var, t in prog.con_events}),
        preprocess=True,
    )
    reachable_states = [Variable(s) for s in new_prog.states]
    prog_old_to_new_state = {
        i: {prev: new.intersection(reachable_states) for prev, new in d.items()}
        for i, d in prog_old_to_new_state.items()
    }
    return new_prog, prog_old_to_new_state


def program_cross_product_optimized(
    programs: list[Program],
    symbol_table,
    losing_states,
    lose_var,
    name=None,
    *,
    debug: bool = False,
    use_incremental_sat: bool = True,
):
    """Optimized alternative to `program_cross_product`.

    Key differences vs legacy:
    - Builds reachable cross-product states on-the-fly from the initial tuple.
    - Uses SAT-guided recursive transition combination construction with early
      pruning of unsatisfiable partial conjunctions.
    - Orders components by local branching factor to maximize early pruning.
    - Checks losing-source tuples before any SMT work.
    - Avoids redundant SAT filtering in Program preprocessing.
    """
    if len(programs) == 0:
        raise Exception(
            "program_cross_product_optimized: expected at least one program."
        )

    num_programs = len(programs)
    new_initial_state_tuple = tuple(prog.initial_state for prog in programs)
    new_initial_state = "_".join(new_initial_state_tuple)

    # Keep the same mapping shape as the legacy implementation.
    prog_old_to_new_state = {
        i: {Variable(s): set() for s in programs[i].states} for i in range(num_programs)
    }

    new_states = set()
    new_transitions = []
    transition_constraint_cache = {}
    combined_src_cache = {}
    combined_tgt_cache = {}
    lose_state_name = lose_var if lose_var is not None else "lose"

    def _combined_state_name(state_tuple):
        cached = combined_src_cache.get(state_tuple)
        if cached is None:
            cached = "_".join(state_tuple)
            combined_src_cache[state_tuple] = cached
        return cached

    def _combined_target_name(tgt_tuple):
        cached = combined_tgt_cache.get(tgt_tuple)
        if cached is None:
            cached = "_".join(tgt_tuple)
            combined_tgt_cache[tgt_tuple] = cached
        return cached

    def _is_losing_src_tuple(state_tuple) -> bool:
        if "lose" in state_tuple:
            return True
        return any(
            state_tuple[i] in losing_states.get(i, []) for i in range(num_programs)
        )

    def _transition_constraint(t: Transition):
        cached = transition_constraint_cache.get(t)
        if cached is not None:
            return cached
        cached = conjunct(
            transition_formula(t),
            conjunct_formula_set([p.prev_rep() for p in t.pred_upgrades]),
        )
        transition_constraint_cache[t] = cached
        return cached

    worklist = deque([new_initial_state_tuple])
    queued = {new_initial_state_tuple}
    processed = set()

    sat_ctx_cls = (
        IncrementalSatContext if use_incremental_sat else NonIncrementalSatContext
    )
    with sat_ctx_cls(symbol_table) as sat_ctx:
        while worklist:
            state_tuple = worklist.popleft()
            if state_tuple in processed:
                continue
            processed.add(state_tuple)

            # Early source-losing pruning before any SMT checks.
            if _is_losing_src_tuple(state_tuple):
                continue

            possible_transitions = [
                programs[i].state_to_trans.get(state_tuple[i], [])
                for i in range(num_programs)
            ]
            if any(len(ts) == 0 for ts in possible_transitions):
                continue

            order = sorted(
                range(num_programs), key=lambda i: len(possible_transitions[i])
            )
            if debug:
                upper_bound = math.prod(len(possible_transitions[i]) for i in order)
                print("TRAN COMBS UPPER BOUND: " + str(upper_bound))

            selected = [None] * num_programs

            def _emit_combination(transition_combination):
                combined_src = _combined_state_name(state_tuple)
                new_states.add(combined_src)
                for i in range(num_programs):
                    prog_old_to_new_state[i][Variable(state_tuple[i])].add(
                        Variable(combined_src)
                    )

                tgt_tuple = tuple(t.tgt for t in transition_combination)
                if "lose" in tgt_tuple:
                    combined_tgt = lose_state_name
                    new_states.add(combined_tgt)
                    for i in range(num_programs):
                        prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(
                            Variable(combined_tgt)
                        )
                else:
                    losing = [
                        i
                        for i in range(num_programs)
                        if tgt_tuple[i] in losing_states.get(i, [])
                    ]
                    if len(losing) > 0:
                        combined_tgt = lose_state_name
                        new_states.add(combined_tgt)
                        for i in losing:
                            prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(
                                Variable(combined_tgt)
                            )
                    else:
                        combined_tgt = _combined_target_name(tgt_tuple)
                        new_states.add(combined_tgt)
                        for i in range(num_programs):
                            prog_old_to_new_state[i][Variable(tgt_tuple[i])].add(
                                Variable(combined_tgt)
                            )

                        # Reachability-driven state-space construction.
                        if tgt_tuple not in queued and tgt_tuple not in processed:
                            queued.add(tgt_tuple)
                            worklist.append(tgt_tuple)

                combined_condition = conjunct_formula_set(
                    [t.condition for t in transition_combination]
                )
                combined_actions = set()
                combined_outputs = []
                for t in transition_combination:
                    combined_actions.update(t.action)
                    combined_outputs.extend(t.output)

                left_to_u = {}
                # deterministic tie-breaking for conflicting updates
                combined_actions = sorted(
                    combined_actions, key=lambda x: len(x.variablesin())
                )
                for u in combined_actions:
                    if u.left in left_to_u.keys():
                        # conflict, keep deterministic one
                        if not isinstance(u.right, NonDeterministic) and not isinstance(
                            left_to_u[u.left].right, NonDeterministic
                        ):
                            combined_condition = conjunct(
                                combined_condition,
                                BiOp(u.right, "=", left_to_u[u.left].right),
                            )
                        elif not isinstance(u.right, NonDeterministic) and isinstance(
                            left_to_u[u.left].right, NonDeterministic
                        ):
                            left_to_u[u.left] = u
                    else:
                        left_to_u[u.left] = u
                combined_actions = set(left_to_u.values())

                new_t = Transition(
                    combined_src,
                    combined_condition,
                    list(combined_actions),
                    combined_outputs,
                    combined_tgt,
                )
                new_t.pred_upgrades = set(
                    itertools.chain.from_iterable(
                        [tt.pred_upgrades for tt in transition_combination]
                    )
                )
                new_transitions.append(new_t)

            def _dfs_transition_combinations(depth, partial_constraint):
                if depth == num_programs:
                    _emit_combination(selected)
                    return

                prog_idx = order[depth]
                for t in possible_transitions[prog_idx]:
                    selected[prog_idx] = t
                    next_partial = conjunct(
                        partial_constraint, _transition_constraint(t)
                    )
                    if sat(next_partial, symbol_table, sat_ctx=sat_ctx):
                        _dfs_transition_combinations(depth + 1, next_partial)
                selected[prog_idx] = None

            _dfs_transition_combinations(0, true())

    # state set comes from the reachable construction, no consumed iterator bug.
    new_prog = Program(
        name=name if name else "_xprod_".join([prog.name for prog in programs]),
        sts=set(new_states),
        init_st=new_initial_state,
        init_values=list(
            {
                (var.name, symbol_table[var.name])
                for prog in programs
                for var in prog.local_vars
            }
        ),
        transitions=new_transitions,
        env_events=list({(var, t) for prog in programs for var, t in prog.env_events}),
        con_events=list({(var, t) for prog in programs for var, t in prog.con_events}),
        # cross-product generation already performs SAT-guided pruning.
        preprocess=False,
    )
    reachable_states = [Variable(s) for s in new_prog.states]
    prog_old_to_new_state = {
        i: {prev: new.intersection(reachable_states) for prev, new in d.items()}
        for i, d in prog_old_to_new_state.items()
    }
    return new_prog, prog_old_to_new_state


def fill_in_minigames(
    program: Program,
    ltl_formulas: list[Formula],
    to_exclude_from_minigame,
    optimisation_counters: dict[str, int] | None = None,
):
    from programs.minigame_filler import MinigameFiller

    return MinigameFiller(
        program,
        ltl_formulas,
        to_exclude_from_minigame,
        optimisation_counters=optimisation_counters,
    ).run()


def normalise_mg_preds(mg_preds: list[Formula]):
    from programs.minigame_filler import MinigameFiller

    return MinigameFiller.normalise_mg_preds(mg_preds)
