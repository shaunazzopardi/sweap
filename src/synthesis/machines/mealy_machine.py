import config

from graphviz import Digraph
from joblib import Parallel, delayed
from analysis.abstraction.interface.predicate_abstraction import (
    PredicateAbstraction,
)
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from config import env, con
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    disjunct_formula_set,
    neg,
    conjunct,
    dnf_safe,
    propagate_negations,
    simplify_formula_without_math,
    sat,
    project_out_props,
    label_pred,
)
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import (
    AbstractLTLSynthesisProblem,
)
from synthesis.machines.machine import Machine


class MealyMachine(Machine):
    def __init__(
        self,
        name,
        init_index: int,
        env_events,
        con_events,
        env_transitions=None,
        con_transitions=None,
    ):
        self.name = name
        self.init_index = init_index
        self.init_st = "st_" + str(init_index)
        self.states = {self.init_st} | {
            k for k in env_transitions.keys() | con_transitions.keys()
        }
        self.env_events = env_events
        self.con_events = con_events

        if env_transitions is None:
            self.env_transitions = {}
        else:
            self.env_transitions = env_transitions

        if con_transitions is None:
            self.con_transitions = {}
        else:
            self.con_transitions = con_transitions

        self.prog_state = {}
        self.counter = -1
        self.env_transition_tgt = {}
        self.con_transition_tgt = {}
        self.env_prog_state = {}
        self.con_prog_state = {}

    def add_transitions(self, trans_dict: dict, _):
        int_st_index = 0
        interm_states = {}
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            new_src = "st_" + str(src_index)

            env_cond = (env_behaviour.simplify()).to_nuxmv()
            env_cond = propagate_negations(env_cond)

            con_behaviour = disjunct_formula_set(
                trans_dict[(src_index, env_behaviour, tgt_index)]
            )
            con_cond = (con_behaviour.simplify()).to_nuxmv()
            con_cond = propagate_negations(con_cond)
            con_cond_dnf = dnf_safe(con_cond, simplify=False)
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
                new_intermed = "st_" + str(int_st_index)
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

    # TODO add_transitions can be integrated into this
    def add_transitions_env_con_separate(
        self,
        controller: bool,
        trans_dict: dict,
        abstract_ltl_synthesis_problem: AbstractLTLSynthesisProblem,
        abstraction: PredicateAbstraction,
        parallelise=True,
    ):
        # this will create a mealy machine with states tagged by program predicates
        # parallelise=False
        # some preprocessing
        reworked_transitions = []
        if parallelise:
            reworked_transitions = Parallel(n_jobs=-1, prefer="threads", verbose=11)(
                delayed(handle_transition)(
                    src_index,
                    env_behaviour,
                    con_conds,
                    tgt_index,
                    abstract_ltl_synthesis_problem,
                    parallelise=True,
                )
                for (
                    src_index,
                    env_behaviour,
                    tgt_index,
                ), con_conds in trans_dict.items()
            )
        else:
            for (
                src_index,
                env_behaviour,
                tgt_index,
            ), con_conds in trans_dict.items():
                reworked_transitions.append(
                    handle_transition(
                        src_index,
                        env_behaviour,
                        con_conds,
                        tgt_index,
                        abstract_ltl_synthesis_problem,
                        parallelise=False,
                    )
                )

        env_states = {}
        con_states = {}
        for env_turn, (
            (src_index, (src_prog_state, prog_outs)),
            cond,
            tgt_index,
        ) in reworked_transitions:
            if env_turn:
                if src_index not in env_states.keys():
                    env_states[src_index] = []

                if (src_prog_state, prog_outs) not in env_states[src_index]:
                    env_states[src_index].append((src_prog_state, prog_outs))
            else:
                if src_index not in con_states.keys():
                    con_states[src_index] = []

                if (src_prog_state, prog_outs) not in con_states[src_index]:
                    con_states[src_index].append((src_prog_state, prog_outs))

        for env_turn, (
            (src_index, (src_prog_state, prog_outs)),
            env_or_con_cond,
            tgt_index,
        ) in reworked_transitions:
            if env_turn:
                state_loc = str(
                    env_states[src_index].index((src_prog_state, prog_outs))
                )
                new_src = "st_" + str(src_index) + "_" + state_loc
                self.prog_state[new_src] = src_prog_state

                if new_src not in self.env_transitions.keys():
                    self.env_transitions[new_src] = set()

                for i in range(len(con_states[tgt_index])):
                    new_tgt = "st_" + str(tgt_index) + "_" + str(i)
                    self.env_transitions[new_src].add((env_or_con_cond, new_tgt))

            else:
                state_loc = str(
                    con_states[src_index].index((src_prog_state, prog_outs))
                )
                new_src = "st_" + str(src_index) + "_" + state_loc
                self.prog_state[new_src] = src_prog_state

                if new_src not in self.con_transitions.keys():
                    self.con_transitions[new_src] = set()

                for i in range(len(env_states[tgt_index])):
                    new_tgt = "st_" + str(tgt_index) + "_" + str(i)
                    self.con_transitions[new_src].add((env_or_con_cond, new_tgt))

        if not controller:
            if len(env_states[self.init_index]) == 1:
                self.init_st = self.init_st + "_0"
            else:
                # this should not be reached
                raise Exception("Not implemented: counterstrategy not deterministic")
        else:
            init_prog_pred_state = conjunct_formula_set(
                [
                    BiOp(Variable(tv.name), "=", tv.value)
                    for tv in abstraction.get_program().valuation
                ]
            )
            found_init_state = False
            for init_sub_state in env_states[self.init_index]:
                pred_state = init_sub_state[0]
                if sat(
                    conjunct(pred_state, init_prog_pred_state),
                    abstraction.get_symbol_table(),
                    add_missing_vars=True,
                ):
                    self.init_st = init_sub_state
                    found_init_state = True
                    break
            if not found_init_state:
                raise Exception("Did not find controller init state.")

        for st in self.env_transitions.keys():
            self.states.add(st)

        for st in self.con_transitions.keys():
            self.states.add(st)

        had_an_effect = True
        while had_an_effect:
            had_an_effect = self.minimize_env_states()
            had_an_effect = had_an_effect or self.minimize_con_states()

    def minimize_env_states(self):
        had_an_effect = False
        # if env_states have the same program state and the same outgoing transitions, then merge them
        for prog_state, srcs in self.env_prog_state.items():
            tgts_map = {}
            for src, tgts in self.env_transitions.items():
                if src in srcs:
                    frozen_tgts = frozenset(tgts)
                    if frozen_tgts not in tgts_map.keys():
                        tgts_map[frozen_tgts] = [src]
                    else:
                        tgts_map[frozen_tgts].append(src)

            for _, srcs in tgts_map.items():
                if len(srcs) > 1:
                    for src in srcs[1:]:
                        self.env_transitions.pop(src)
                        self.states.remove(src)

                    all_con_transitions = self.con_transitions.items()
                    for con_src, con_tgts in all_con_transitions:
                        all_conds = []
                        new_con_tgts = set()
                        for con_cond, env_tgt in con_tgts:
                            if env_tgt in srcs:
                                had_an_effect = True
                                all_conds.append(con_cond)
                            else:
                                new_con_tgts.add((con_cond, env_tgt))
                        if len(all_conds) > 0:
                            self.con_transitions[con_src] = new_con_tgts
                            new_cond = disjunct_formula_set(all_conds)
                            new_cond = simplify_formula_without_math(new_cond)
                            self.con_transitions[con_src].add((new_cond, srcs[0]))
        return had_an_effect

    def minimize_con_states(self):
        had_an_effect = False
        # if con_states have the same program state and the same outgoing transitions, then merge them
        for prog_state, srcs in self.con_prog_state.items():
            tgts_map = {}
            for src, tgts in self.con_transitions.items():
                if src in srcs:
                    frozen_tgts = frozenset(tgts)
                    if frozen_tgts not in tgts_map.keys():
                        tgts_map[frozen_tgts] = [src]
                    else:
                        tgts_map[frozen_tgts].append(src)

            for _, srcs in tgts_map.items():
                if len(srcs) > 1:
                    for src in srcs[1:]:
                        self.con_transitions.pop(src)
                        self.states.remove(src)

                    all_env_transitions = self.env_transitions.items()
                    for con_src, con_tgts in all_env_transitions:
                        all_conds = []
                        new_con_tgts = set()
                        for con_cond, env_tgt in con_tgts:
                            if env_tgt in srcs:
                                had_an_effect = True
                                all_conds.append(con_cond)
                            else:
                                new_con_tgts.add((con_cond, env_tgt))
                        if len(all_conds) > 0:
                            self.env_transitions[con_src] = new_con_tgts
                            new_cond = disjunct_formula_set(all_conds)
                            new_cond = simplify_formula_without_math(new_cond)
                            self.env_transitions[con_src].add((new_cond, srcs[0]))
        return had_an_effect
        # #     #TODO this optimisation needs to move to minimize function, cannot do it before constructing the whole mealy machine.
        # if (con_action, new_tgt) in con_transition_tgt.keys() and \
        #         prog_state_before_con_action == self.prog_state[con_transition_tgt[(con_action, new_tgt)]]:
        #     if new_src in self.env_transition_tgt.keys():
        #         prev_env_trans = self.env_transition_tgt[new_src]
        #         self.env_transition_tgt.pop(new_src)
        #     else:
        #         prev_env_trans = []
        #
        #     old_env_tgt = new_src
        #     new_src = con_transition_tgt[(con_action, new_tgt)]
        #     new_env_trans = []
        #     for (src, env_cond_without_turn_var) in prev_env_trans:
        #         int_env_trans[src].remove((env_cond_without_turn_var, old_env_tgt))
        #         int_env_trans[src].add((env_cond_without_turn_var, new_src))
        #         new_env_trans.append((env_cond_without_turn_var, new_src))
        #
        #     if new_src in self.env_transition_tgt.keys():
        #         self.env_transition_tgt[new_src] += new_env_trans
        #     else:
        #         self.env_transition_tgt[new_src] = new_env_trans

    def __str__(self):
        return str(self.to_dot())

    def to_dot(self, pred_list: [Formula] = None):
        to_replace = []
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace += [BiOp(pred_var, ":=", pred)]

        dot = Digraph(
            name="MealyMachine",
            graph_attr=[
                ("overlap", "scalexy"),
                ("splines", "true"),  # ("rankdir", "LR"),
                ("ranksep", "0.8"),
                ("nodesep", "0.5"),
            ],
            node_attr=[("shape", "circle")],
            edge_attr=[("fontname", "mono")],
            engine="dot",
            format="svg",
        )

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            if s in self.prog_state.keys():
                prog_state = self.prog_state[s]
                dot.node(str(s), str(prog_state))
            else:
                dot.node(str(s))

        dot.edge("init", str(self.init_st), style="solid")

        for src in self.env_transitions.keys():
            for beh, tgt in self.env_transitions.get(src):
                label = str(beh.replace_vars(to_replace))
                dot.edge(str(src), str(tgt), label)

        for src in self.con_transitions.keys():
            for beh, tgt in self.con_transitions.get(src):
                label = str(beh.replace_vars(to_replace))
                dot.edge(str(src), str(tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(
        self, prog_states, prog_out_events, state_pred_list, trans_pred_list
    ):
        state_pred_acts = [p.bool_var for p in state_pred_list]
        trans_pred_acts = [t for p in trans_pred_list for t in p.bool_rep.values()]
        pred_acts = state_pred_acts + trans_pred_acts

        guards_acts = {}

        init_cond = conjunct_formula_set(
            [neg(Variable(stt)) for stt in self.states if stt != self.init_st]
            + [Variable(self.init_st)]
        )
        init_cond = conjunct(
            init_cond,
            conjunct_formula_set([neg(Variable(t)) for t in trans_pred_acts]),
        )

        for src in self.env_transitions.keys():
            for env_beh, env_tgt in self.env_transitions.get(src):
                for con_beh, tgt in self.con_transitions.get(env_tgt):
                    guard = str(src) + " & " + str(env_beh) + " & " + str(con_beh)
                    if guard not in guards_acts.keys():
                        guards_acts[guard] = list()

                    act = conjunct_formula_set(
                        [
                            UniOp("next", Variable(tgt)),
                            UniOp(
                                "next",
                                conjunct_formula_set(
                                    [neg(Variable(s)) for s in self.states if s != tgt]
                                ),
                            ),
                        ]
                    ).to_nuxmv()

                    guards_acts[guard].append(act)

        define = []
        transitions = []
        guard_ids = []
        i = 0
        guard_keys = list(guards_acts.keys())
        while i < len(guard_keys):
            define += [self.name + "_guard_" + str(i) + " := " + guard_keys[i]]
            define += [
                self.name
                + "_act_"
                + str(i)
                + " := ("
                + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]]))
                + ")"
            ]
            transitions.append(
                self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i)
            )
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += [
            "next(" + str(event) + ") = " + str(event)
            for event in (self.env_events + self.con_events)
            if Variable(str(event)) not in (prog_out_events + prog_states + pred_acts)
        ]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        vars = ["turn : {prog, cs}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [
            str(var) + " : boolean"
            for var in self.env_events
            if str(var)
            not in [str(v) for v in (prog_out_events + prog_states + pred_acts)]
        ]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["prog_" + str(var) + " : boolean" for var in prog_out_events]
        vars += [str(var) + " : boolean" for var in prog_states]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions = ["((" + ")\n\t|\t(".join(transitions) + "))"]

        identity = (
            "((turn = cs) -> (identity_"
            + self.name
            + " & "
            + str(
                conjunct_formula_set(
                    [
                        BiOp(
                            UniOp("next", Variable("prog_" + e.name)),
                            "=",
                            Variable("prog_" + e.name),
                        )
                        for e in prog_out_events
                    ]
                    + [
                        BiOp(
                            UniOp("next", Variable(str(p))),
                            "=",
                            Variable(str(p)),
                        )
                        for p in prog_states + pred_acts
                    ]
                ).to_nuxmv()
            )
            + "))"
        )

        trans = [
            "("
            + identity
            + " &\n\t\t((turn = prog) -> ("
            + ")\n\t|\t(".join(transitions)
            + ")))"
        ]
        invar = ["TRUE"]
        # # invar = mutually_exclusive_rules(self.states)
        # invar = mutually_exclusive_rules(["prog_" + s for s in prog_states])
        # invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]
        # j = 0
        # while j < len(trans_pred_acts):
        #     invar += [str(neg(conjunct(trans_pred_acts[j], trans_pred_acts[j + 1])))]
        #     j += 2

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    def to_nuXmv_with_turns_for_con_verif(
        self, prog_states, prog_out_events, state_pred_list, trans_pred_list
    ):
        state_pred_acts = [p.bool_var for p in state_pred_list]
        trans_pred_acts = [t for p in trans_pred_list for t in p.bool_rep.values()]
        pred_acts = state_pred_acts + trans_pred_acts

        guards_acts = {}

        init_cond = conjunct_formula_set(
            [neg(Variable(stt)) for stt in self.states if stt != self.init_st]
            + [Variable(self.init_st)]
        )
        init_cond = conjunct(
            init_cond,
            conjunct_formula_set([neg(Variable(t)) for t in trans_pred_acts]),
        )

        for src in self.env_transitions.keys():
            for env_beh, env_tgt in self.env_transitions.get(src):
                for con_beh, tgt in self.con_transitions.get(env_tgt):
                    guard = str(src) + " & " + str(env_beh) + " & " + str(con_beh)
                    if guard not in guards_acts.keys():
                        guards_acts[guard] = list()

                    act = conjunct_formula_set(
                        [
                            UniOp("next", Variable(tgt)),
                            UniOp(
                                "next",
                                conjunct_formula_set(
                                    [neg(Variable(s)) for s in self.states if s != tgt]
                                ),
                            ),
                        ]
                    ).to_nuxmv()

                    guards_acts[guard].append(act)

        define = []
        transitions = []
        guard_ids = []
        i = 0
        guard_keys = list(guards_acts.keys())
        while i < len(guard_keys):
            define += [self.name + "_guard_" + str(i) + " := " + guard_keys[i]]
            define += [
                self.name
                + "_act_"
                + str(i)
                + " := ("
                + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]]))
                + ")"
            ]
            transitions.append(
                self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i)
            )
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += [
            "next(" + str(event) + ") = " + str(event)
            for event in (self.env_events + self.con_events)
            if Variable(str(event)) not in (prog_out_events + prog_states + pred_acts)
        ]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        vars = []
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [
            str(var) + " : boolean"
            for var in self.env_events
            if str(var)
            not in [str(v) for v in (prog_out_events + prog_states + pred_acts)]
        ]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["prog_" + str(var) + " : boolean" for var in prog_out_events]
        vars += [str(var) + " : boolean" for var in prog_states]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions = ["((" + ")\n\t|\t(".join(transitions) + "))"]

        trans = ["(" + ")\n\t|\t(".join(transitions) + ")"]
        invar = ["TRUE"]
        # # invar = mutually_exclusive_rules(self.states)
        # invar = mutually_exclusive_rules(["prog_" + s for s in prog_states])
        # invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]
        # j = 0
        # while j < len(trans_pred_acts):
        #     invar += [str(neg(conjunct(trans_pred_acts[j], trans_pred_acts[j + 1])))]
        #     j += 2

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    def to_nuXmv_with_turns_old(
        self, mon_states, mon_out_events, state_pred_list, trans_pred_list
    ):
        state_pred_acts = [label_pred(p, state_pred_list) for p in state_pred_list]
        trans_pred_acts = [label_pred(p, trans_pred_list) for p in trans_pred_list]
        pred_acts = state_pred_acts + trans_pred_acts

        mon_events = mon_out_events + [Variable(s) for s in mon_states]

        new_mon_events = [
            BiOp(m, ":=", Variable("mon_" + m.name)) for m in mon_events
        ] + [BiOp(m, ":=", Variable(m.name)) for m in pred_acts]

        guards_acts = {}

        init_conds = []

        for env_beh, tgt in self.env_transitions.get(self.init_st):
            formula_set = [env_beh.replace(new_mon_events), Variable(tgt)] + [
                neg(Variable(st)) for st in self.states if st != tgt
            ]
            if tgt in self.prog_state.keys():
                formula_set.append(self.prog_state[tgt].replace_vars(new_mon_events))
            init_conds += [conjunct_formula_set(formula_set)]

        init_cond = disjunct_formula_set(init_conds)
        for src in self.con_transitions.keys():
            for con_behaviour, con_tgt in self.con_transitions[src]:
                guard = "turn = mon_env & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()
                act = (
                    "next("
                    + str(con_behaviour.replace(new_mon_events).to_nuxmv())
                    + " & "
                    + str(con_tgt)
                    + " & "
                    + " & ".join(["!" + st for st in self.states if st != con_tgt])
                    + ")"
                )
                if len(self.prog_state.keys()) == 0:
                    act += (
                        "& next("
                        + " & ".join(["!" + str(o) for o in mon_out_events])
                        + ")"
                    )
                else:
                    act += (
                        "& next("
                        + str(
                            self.prog_state[con_tgt]
                            .replace_vars(new_mon_events)
                            .to_nuxmv()
                        )
                        + ")"
                    )
                guards_acts[guard].append(act)
                if (con_tgt not in self.env_transitions.keys()) or len(
                    self.env_transitions.get(con_tgt)
                ) == 0:
                    raise Exception(
                        "Nothing to do in counter-strategy from state " + str(con_tgt)
                    )

        for src in self.env_transitions.keys():
            for env_beh, env_tgt in self.env_transitions.get(src):
                guard = "turn = mon_con & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()

                if len(self.prog_state.keys()) == 0:
                    act = (
                        "next("
                        + str(env_beh.replace(new_mon_events).to_nuxmv())
                        + " & "
                        + str(env_tgt)
                        + " & "
                        + " & ".join(["!" + st for st in self.states if st != env_tgt])
                        + ")"
                    )
                else:
                    act = conjunct_formula_set(
                        [
                            UniOp("next", env_beh),
                            UniOp(
                                "next",
                                self.prog_state[env_tgt].replace_vars(new_mon_events),
                            ),
                            UniOp("next", Variable(env_tgt)),
                            UniOp(
                                "next",
                                conjunct_formula_set(
                                    [
                                        neg(Variable(s))
                                        for s in self.states
                                        if s != env_tgt
                                    ]
                                ),
                            ),
                        ]
                    ).to_nuxmv()

                guards_acts[guard].append(act)

        define = []
        transitions = []
        guard_ids = []
        i = 0
        guard_keys = list(guards_acts.keys())
        while i < len(guard_keys):
            define += [self.name + "_guard_" + str(i) + " := " + guard_keys[i]]
            define += [
                self.name
                + "_act_"
                + str(i)
                + " := ("
                + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]]))
                + ")"
            ]
            transitions.append(
                self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i)
            )
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += [
            "next(" + str(event) + ") = " + str(event)
            for event in (self.env_events + self.con_events)
            if Variable(str(event)) not in (mon_events + pred_acts)
        ]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name + "& next(mismatch)")

        vars = ["turn : {env, mon_env, con, mon_con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [
            str(var) + " : boolean"
            for var in self.env_events
            if str(var) not in [str(v) for v in (mon_events + pred_acts)]
        ]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["mon_" + str(var) + " : boolean" for var in mon_events]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions = ["((" + ")\n\t|\t(".join(transitions) + "))"]

        identity = (
            "((turn = env | turn = con) -> (identity_"
            + self.name
            + " & "
            + str(
                conjunct_formula_set(
                    [
                        BiOp(
                            UniOp("next", Variable("mon_" + e.name)),
                            "=",
                            Variable("mon_" + e.name),
                        )
                        for e in mon_events
                    ]
                    + [
                        BiOp(
                            UniOp("next", Variable(p.name)),
                            "=",
                            Variable(p.name),
                        )
                        for p in pred_acts
                    ]
                ).to_nuxmv()
            )
            + "))"
        )

        trans = [
            "("
            + identity
            + " &\n\t\t(!(turn = env | turn = con) -> ("
            + ")\n\t|\t(".join(transitions)
            + ")))"
        ]
        invar = ["TRUE"]
        # # invar = mutually_exclusive_rules(self.states)
        # invar = mutually_exclusive_rules(["mon_" + s for s in mon_states])
        # invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]
        # j = 0
        # while j < len(trans_pred_acts):
        #     invar += [str(neg(conjunct(trans_pred_acts[j], trans_pred_acts[j + 1])))]
        #     j += 2

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    def to_moore_machine(self):
        if not config.Config.getConfig().dual:
            raise Exception(
                "This function is meant to transform a controller into a counterstrategy "
                "only when the --dual flag is used."
            )

        raise NotImplementedError(
            "Not implemented MealyMachine for dual problem to MooreMachine translation yet."
        )
        # init_trans = []
        # for env_beh, tgt in self.env_transitions[self.init_st]:
        #     # pred_state here becomes associated with init_st
        #     # env_events ignored
        #     # con_events become new env_events
        #     env_act = env_beh
        #     for con_beh, con_tgt in self.con_transitions[tgt]:
        #
        # print()
        # pass


def handle_transition(
    src_index,
    env_cond,
    con_conds,
    tgt_index,
    abstract_problem: AbstractLTLSynthesisProblem,
    parallelise=False,
):
    pure_env_events = abstract_problem.get_env_props()
    prog_out = abstract_problem.get_program_out_props()
    prog_preds = abstract_problem.get_program_pred_props()

    env_cond = (env_cond.simplify()).to_nuxmv()
    env_cond = propagate_negations(env_cond)

    env_turn = sat(conjunct(env, env_cond))
    con_turn = sat(conjunct(con, env_cond))

    if not env_turn and not con_turn:
        breaking_assumptions = True
        raise Exception(
            "Environment is breaking the turn logic assumption in transition: "
            + str(src_index)
            + " "
            + str(env_cond)
            + " "
            + ", ".join(map(str, con_conds))
            + " "
            + str(tgt_index)
        )

    # TODO need to populate self.env_prog_state and self.con_prog_state to minimize

    src_prog_state = project_out_props(env_cond, pure_env_events + [env])

    if env_turn:
        pure_env_cond = project_out_props(env_cond, prog_out + prog_preds + [env])
        new_transition = (
            (src_index, (src_prog_state, None)),
            pure_env_cond,
            tgt_index,
        )
        return True, new_transition

    if con_turn:
        prog_outs = project_out_props(
            propagate_negations(env_cond), pure_env_events + prog_preds + [env]
        ).simplify()
        prog_outs = simplify_formula_without_math(prog_outs)

        new_con_conds = []
        for con_cond_orig in con_conds:
            con_cond = (con_cond_orig.simplify()).to_nuxmv()
            new_con_conds.append(con_cond)
        new_con_cond = simplify_formula_without_math(
            disjunct_formula_set(new_con_conds)
        )

        new_transition = (
            (src_index, (src_prog_state, prog_outs)),
            new_con_cond,
            tgt_index,
        )

        return False, new_transition
