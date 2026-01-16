import itertools
import logging
from multiprocessing import Pool
from textwrap import dedent
from typing import Set, Union

from graphviz import Digraph
import config
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from programs.dfa import program_sccs, reachable_states
from programs.transition import Transition
from prop_lang.formula import Formula
from prop_lang.types.values import BoolAtoms
from prop_lang.util import (
    reset_caches as prop_lang_util_reset_caches,
)
from programs.util import (
    reset_caches,
    stutter_transition,
    symbol_table_from_program,
    is_deterministic,
    binary_rep_states,
    add_prev_suffix,
    transition_formula,
    binary_rep,
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
    ):
        config.Config.getConfig().cache_smt = False
        reset_caches()

        if not name:
            raise Exception("Program must have a name.")
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.constants = {}

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
            tt.complete_outputs(self.out_events).complete_action_set(all_vars)
            for t in self.transitions
            for tt in self.add_type_constraints_to_guards(t)
        ]

        # Intervals are encoded in program logic, so we can drop them from symbol table
        # TODO: not doing this can cause controllers that are not correct
        #       e.g., elevator-paper-10, reversible-lane-r-5.prog, robot-grid-reach-2d-5.prog,
        #       reversible-lane-r-10.prog, reversible-lane-r-50.prog
        #       Why?
        # TODO: why does this problem not also arise for natural types?
        new_symbol_table = {}
        for v, t in self.symbol_table.items():
            if isinstance(t, Number) and t.interval:
                new_symbol_table[v] = Number(
                    t.number_type,
                    None,
                )
            else:
                new_symbol_table[v] = t

        self.symbol_table = new_symbol_table

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

        reachable_statess = reachable_states(self)
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
        for transition in self.transitions:
            if dualise:
                # cond = (
                #     transition.condition.to_nuxmv()
                # )
                cond = massage_ltl_for_dual(
                    transition.condition, [v for v, _ in self.env_events], False
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
        for var in self.local_vars:
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

        if dualise:
            vars = ["turn : {prog, cs, init1, init2}"]
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
                ["next(" + str(var) + "_prev) = " + str(var) for var in self.local_vars]
            )
            if len(self.local_vars) > 0
            else ""
        )
        maintain_prevs = "!(turn = cs)" + (
            " & "
            + " & ".join(
                [
                    "next(" + str(var) + "_prev) = " + str(var) + "_prev"
                    for var in self.local_vars
                ]
            )
            if len(self.local_vars) > 0
            else ""
        )
        prev_logic = "((" + update_prevs + ") | (" + maintain_prevs + "))"
        trans += [prev_logic]

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [
            str(var) + " >= 0"
            for var in self.local_vars
            if self.symbol_table[var.name] == NATURAL
        ]
        invar.extend(
            [
                var + "_prev" + " >= 0"
                for var in self.local_vars_str
                if self.symbol_table[var] == NATURAL
            ]
        )
        # add interval constraints

        invar.extend(
            [
                str(var)
                + (">= " if n.interval.lower_inclusive else ">")
                + str(n.interval.lower)
                for var in self.local_vars
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
                for var in self.local_vars
                if isinstance(n := self.symbol_table[str(var)], Number)
                and n.interval
                and n.interval.upper != ""
            ]
        )

        invar.extend(
            [
                str(var) + " >= 0"
                for var in self.num_in_out
                if self.symbol_table[str(var)] == NATURAL
            ]
        )
        invar.extend(
            [
                str(var) + "_prev" + " >= 0"
                for var in self.num_in_out
                if self.symbol_table[str(var)] == NATURAL
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
                # cond = (
                #     transition.condition.to_nuxmv()
                # )
                cond = massage_ltl_for_dual(
                    transition.condition, [v for v, _ in self.env_events], False
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
        for var in self.local_vars_str:
            identity.append("next(" + var + ") = " + var)
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
            else:
                raise Exception("Unsupported type for variable: " + str(var_type))

            prev_logic += ["next(" + str(var) + "_prev) = " + str(var)]

        vars += [str(var) + " : boolean" for var in self.out_events + self.bool_in_out]

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
            var + " >= 0"
            for var in self.local_vars_str
            if self.symbol_table[var] == NATURAL
        ]
        invar.extend(
            [
                var + "_prev" + " >= 0"
                for var in self.local_vars_str
                if self.symbol_table[var] == NATURAL
            ]
        )
        invar.extend(
            [
                str(var) + " >= 0"
                for var in self.num_in_out
                if self.symbol_table[str(var)] == NATURAL
            ]
        )

        invar.extend(
            [
                str(var)
                + (">= " if n.interval.lower_inclusive else ">")
                + str(n.interval.lower)
                for var in self.local_vars
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
                for var in self.local_vars
                if isinstance(n := self.symbol_table[str(var)], Number)
                and n.interval
                and n.interval.upper != ""
            ]
        )
        invar.extend(
            [
                str(var) + "_prev" + " >= 0"
                for var in self.num_in_out
                if self.symbol_table[str(var)] == NATURAL
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
                        left_to_u[u.left], NonDeterministic
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


def fill_in_minigames(
    program: Program, ltl_formulas: list[Formula], to_exclude_from_minigame
):
    no_mini_games_added = True
    no_losing_state_modifications = True
    to_add_to_local_vars = set()
    bool_updates = set()
    var_to_minigame_state = {}
    minigame_states = set()
    new_states = []
    new_trans = []
    new_con_events = set()
    ts_to_remove = []

    mini_game_counter = 0
    existing_mini_games_from_with: dict[
        str, dict[tuple[frozenset[Variable], Formula], str]
    ] = {}
    to_exclude_from_minigame = list(to_exclude_from_minigame)
    for t in program.transitions:
        non_determined_updates = [
            a for a in t.action if isinstance(a.right, NonDeterministic)
        ]
        if len(non_determined_updates) == 0:
            new_trans.append(t)
            continue

        if (t.src in to_exclude_from_minigame) or (
            t.tgt in to_exclude_from_minigame and len(t.pred_upgrades) == 0
        ):
            no_losing_state_modifications = True
            new_t = Transition(
                t.src,
                t.condition,
                [a for a in t.action if a not in non_determined_updates],
                [],
                to_exclude_from_minigame[0],
            )
            new_trans.append(new_t)
            continue

        if any(
            v
            for p in t.pred_upgrades
            for v in p.variablesin()
            if v in program.num_in_out
        ):
            raise Exception(
                "We do not support minigames with numerical inputs/outputs yet."
            )

        undetermined_vars: frozenset[Variable] = frozenset(
            u.left for u in non_determined_updates
        )
        mg_preds_key = conjunct_formula_set(p.prev_rep() for p in t.pred_upgrades)
        minigame_params = (undetermined_vars, mg_preds_key)
        if (
            t.tgt in existing_mini_games_from_with.keys()
            and minigame_params in existing_mini_games_from_with[t.tgt].keys()
        ):
            start_state = existing_mini_games_from_with[t.tgt][minigame_params]
            new_t = Transition(
                t.src,
                t.condition,
                [a for a in t.action if a not in non_determined_updates],
                [],
                start_state,
            )
            new_trans.append(new_t)
            continue

        # need to create enough controller events to represent the minigame choices
        raw_events = (
            [u.left.name + "_inc" for u in non_determined_updates]
            + [u.left.name + "_dec" for u in non_determined_updates]
            + ["stop"]
        )

        con_bin_vars, bin_map = binary_rep(raw_events, "minigame_event_")
        to_replace = {}
        current_con_events = list(set(program.con_events) | new_con_events)
        vars_to_reuse = (
            len(con_bin_vars)
            if len(current_con_events) >= len(con_bin_vars)
            else len(current_con_events)
        )
        for i in range(vars_to_reuse):
            to_replace[con_bin_vars[i]] = current_con_events[i][0]
            con_bin_vars[i] = current_con_events[i][0]

        bin_map = {k: v.replace_formulas(to_replace) for k, v in bin_map.items()}
        new_con_events.update({(var, BOOLEAN) for var in con_bin_vars})
        stop = bin_map["stop"]

        # create minigame transitions
        start_state = t.tgt + "_minigame_" + str(mini_game_counter)
        minigame_states.add(Variable(start_state))
        new_states.append(start_state)
        end_state = t.tgt
        new_t = Transition(
            t.src,
            t.condition,
            [a for a in t.action if a not in non_determined_updates],
            [],
            start_state,
        )
        mg_preds = t.pred_upgrades
        mg_preds_key = conjunct_formula_set(t.pred_upgrades)
        undet_vars = []

        to_replace_preds = {}
        for u in non_determined_updates:
            v = u.left
            if program.symbol_table[str(u.left)] == BOOLEAN:
                bool_updates.add(v)
                continue
            int_v = Variable("int_" + str(v))
            to_replace_preds[v] = int_v

        stop_prop = conjunct_formula_set(
            p.prev_rep().replace_formulas(to_replace_preds) for p in mg_preds
        )

        minigame_params: tuple[frozenset[Variable], Formula] = (
            undetermined_vars,
            mg_preds_key,
        )
        if end_state in existing_mini_games_from_with.keys():
            if minigame_params in existing_mini_games_from_with[end_state].keys():
                start_state = existing_mini_games_from_with[end_state][minigame_params]
            else:
                existing_mini_games_from_with[end_state][minigame_params] = start_state
        else:
            existing_mini_games_from_with[end_state] = {minigame_params: start_state}

        for u in non_determined_updates:
            no_mini_games_added = False
            v = u.left
            if v in var_to_minigame_state.keys():
                var_to_minigame_state[v].append(Variable(start_state))
            else:
                var_to_minigame_state[v] = [Variable(start_state)]
            undet_vars.append(v)

            inc_prop = bin_map[(v.name + "_inc")]
            dec_prop = bin_map[(v.name + "_dec")]

            if v in bool_updates:
                # inc_transition
                inc_t = Transition(
                    start_state,
                    inc_prop,
                    [Update(v, Value(BoolAtoms.TRUE))],
                    [],
                    start_state,
                )
                dec_t = Transition(
                    start_state,
                    dec_prop,
                    [Update(v, Value(BoolAtoms.FALSE))],
                    [],
                    start_state,
                )
                new_trans.append(inc_t)
                new_trans.append(dec_t)
            else:
                int_v = Variable("int_" + str(v))
                to_add_to_local_vars.add((v, int_v))

                new_t.action.append(Update(int_v, v))
                new_t.action.append(Update(v, v))
                # inc_transition
                inc_t = Transition(
                    start_state,
                    inc_prop,
                    [Update(int_v, BiOp(int_v, "+", Value(1)))],
                    [],
                    start_state,
                )
                dec_t = Transition(
                    start_state,
                    dec_prop,
                    [Update(int_v, BiOp(int_v, "-", Value(1)))],
                    [],
                    start_state,
                )
                if sat(neg(stop_prop), program.symbol_table):
                    stutter_t = Transition(
                        start_state,
                        conjunct(stop, neg(stop_prop)),
                        [],
                        [],
                        start_state,
                    )
                    new_trans.append(stutter_t)
                new_trans.append(inc_t)
                new_trans.append(dec_t)

        stop_t = Transition(
            start_state,
            conjunct(stop, stop_prop),
            [
                Update(v, Variable("int_" + str(v)))
                for v in undet_vars
                if v not in bool_updates
            ]
            + [
                Update(Variable("int_" + str(v)), Value(0))
                for v in undet_vars
                if v not in bool_updates
            ],
            [],
            end_state,
        )
        new_trans.append(stop_t)

        mini_game_counter += 1
        new_trans.append(new_t)
        ts_to_remove.append(t)

    if no_mini_games_added:
        reset_caches()
        prop_lang_util_reset_caches()
        for t in new_trans:
            for tt in new_trans:
                if t == tt or t.src != tt.src:
                    continue
                elif sat(
                    conjunct(t.condition, tt.condition),
                    program.symbol_table
                    | {
                        str(v): BOOLEAN
                        for v in minigame_states | {v[0] for v in new_con_events}
                    },
                ):
                    raise Exception(
                        "Conflict in minigame transitions between \n"
                        + str(t)
                        + "\nand\n"
                        + str(tt)
                    )
        new_prog = Program(
            name=program.name,
            sts=program.states,
            init_st=program.initial_state,
            init_values=list(
                {
                    (var.name, program.symbol_table[var.name])
                    for var in program.local_vars
                }
            ),
            transitions=new_trans,
            env_events=program.env_events,
            con_events=program.con_events,
            preprocess=False,
        )
        return new_prog, {}, []

    new_init_var_values = {
        (
            str(int_v),
            program.symbol_table[str(v)],
            Value(0) if v not in bool_updates else Value(False),
        )
        for v, int_v in to_add_to_local_vars
    }

    for t in new_trans:
        for tt in new_trans:
            if t == tt or t.src != tt.src:
                continue
            elif sat(
                conjunct(t.condition, tt.condition),
                program.symbol_table
                | {
                    str(v): BOOLEAN
                    for v in minigame_states | {v[0] for v in new_con_events}
                },
            ):
                raise Exception(
                    "Conflict in minigame transitions between \n"
                    + str(t)
                    + "\nand\n"
                    + str(tt)
                )

    # now, for each pred in ltl_spec that involves non_determined_updates, we need to
    # replace it with a formula that accounts for the minigame
    # e.g., G (x' < 5) becomes G ( in_minigame U !in_minigame & (x < 5) )
    # where in_minigame is a formula that is true when in any of the minigame states
    # and add guarantee GF(!in_minigame) to ensure we eventually exit minigame

    preds_in_ltl = set()
    for ltl in ltl_formulas:
        preds_in_ltl.update(atomic_predicates(ltl))
    preds_to_replace = {}
    for p in preds_in_ltl:
        undet_vars_in_p = [
            v for v in p.variablesin() if v in var_to_minigame_state.keys()
        ]
        if len(undet_vars_in_p) == 0:
            continue
        relevant_minigame_states = set()
        for v in undet_vars_in_p:
            relevant_minigame_states.update(var_to_minigame_state[v])
        in_minigame = disjunct_formula_set(relevant_minigame_states)
        new_p = BiOp(in_minigame, "U", conjunct(neg(in_minigame), p))
        preds_to_replace[p] = new_p

    reset_caches()
    prop_lang_util_reset_caches()
    new_prog = Program(
        name=program.name,
        sts=program.states | set(new_states),
        init_st=program.initial_state,
        init_values=list(
            {(var.name, program.symbol_table[var.name]) for var in program.local_vars}
            | new_init_var_values
        ),
        transitions=new_trans,
        env_events=program.env_events,
        con_events=list(set(program.con_events) | new_con_events),
        preprocess=False,
    )
    return new_prog, preds_to_replace, list(minigame_states)
