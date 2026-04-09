import config

from graphviz import Digraph
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from config import env, con
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    disjunct_formula_set,
    is_tautology,
    massage_ltl_for_dual,
    neg,
    conjunct,
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
    ):
        self.name = name
        self.init_index = init_index
        self.init_st = "st_" + str(init_index)
        self.states = {self.init_st}
        self.env_events = env_events
        self.con_events = con_events

        self.transitions = {}

    def add_transitions(self, trans_dict: dict, symbol_table=None):
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            new_src = "st_" + str(src_index)
            new_tgt = "st_" + str(tgt_index)

            env_cond = env_behaviour.simplify()
            env_cond = propagate_negations(env_cond)

            con_behaviour = disjunct_formula_set(
                trans_dict[(src_index, env_behaviour, tgt_index)]
            )
            con_cond = con_behaviour.simplify()
            con_cond = propagate_negations(con_cond)
            # con_cond_dnf = dnf_safe(con_cond, simplify=False)
            # if isinstance(con_cond_dnf, BiOp) and con_cond_dnf.op == "|":
            #     con_conds = con_cond_dnf.sub_formulas_up_to_associativity()
            # else:
            #     con_conds = [con_cond_dnf]

            if new_src not in self.transitions.keys():
                self.transitions[new_src] = {}
                self.transitions[new_src][new_tgt] = set()
            elif new_tgt not in self.transitions[new_src].keys():
                self.transitions[new_src][new_tgt] = set()

            self.transitions[new_src][new_tgt].add((env_cond, con_cond))

            self.states.add(new_src)
            self.states.add(new_tgt)

    def __str__(self):
        return str(self.to_dot())

    def to_dot(self, pred_list=None):
        to_replace = {}
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace[pred_var] = pred

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
            dot.node(str(s))

        dot.edge("init", str(self.init_st), style="solid")

        for src in self.transitions.keys():
            for tgt in self.transitions[src].keys():
                for env_beh, con_beh in self.transitions[src][tgt]:
                    label = (
                        str(env_beh.replace_vars(to_replace))
                        + " / "
                        + str(con_beh.replace_vars(to_replace))
                    )
                    dot.edge(str(src), str(tgt), label)

        return dot

    def to_nuXmv_with_turns(
        self, prog_states, prog_out_events, state_pred_list, trans_pred_list
    ):
        dual2 = config.Config.getConfig().dual2
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

        f = lambda x: (
            UniOp("next", x) if (str(x).startswith("bin_") or x in pred_acts) else None
        )

        init_transitions = []
        for src in self.transitions.keys():
            for tgt, env_con_behs in self.transitions[src].items():
                for env_beh, con_beh in env_con_behs:
                    if dual2:
                        con_beh = con_beh.replace_formulas(f).to_nuxmv()
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

                    if src == self.init_st:
                        init_transitions.append(guard + " & " + act)
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

        if dual2:
            vars = ["turn : {cs, init1}"]
        else:
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
            + (
                identity
                if not dual2
                else "((turn = init1) -> ((" + ") | (".join(init_transitions) + ")))"
            )
            + " &\n\t\t("
            + ("(turn != cs)" if not dual2 else "(turn != init1)")
            + " -> ("
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

    def to_nuXmv_with_turns_for_verif(
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

        debug = config.Config.getConfig().debug
        for src in self.transitions.keys():
            if debug:
                ecs = [
                    ec
                    for env_con_behs in self.transitions[src].values()
                    for ec, _ in env_con_behs
                ]
                c = disjunct_formula_set(ecs)
                symbol_table = {str(v): BOOLEAN for v in c.variablesin()}
                if not is_tautology(
                    c,
                    symbol_table,
                ):
                    raise Exception(
                        str(src)
                        + " does not have complete transitions for environment behaviour."
                    )
                for e1 in ecs:
                    for e2 in ecs:
                        if e1 != e2:
                            c = conjunct(e1, e2)
                            symbol_table = {str(v): BOOLEAN for v in c.variablesin()}
                            if sat(c, symbol_table):
                                raise Exception(
                                    str(src)
                                    + " has overlapping transitions for environment behaviour: "
                                    + str(e1)
                                    + " and "
                                    + str(e2)
                                )
            for tgt, env_con_behs in self.transitions[src].items():
                if debug:
                    symbol_table = {}
                    for ec, _ in env_con_behs:
                        for ecc, _ in env_con_behs:
                            if ec != ecc:
                                c = conjunct(ec, ecc)
                                symbol_table |= {
                                    str(v): BOOLEAN for v in c.variablesin()
                                }
                                if sat(c, symbol_table):
                                    raise Exception(
                                        str(src)
                                        + " has conflicting transitions: "
                                        + str(ec)
                                        + " and "
                                        + str(ecc)
                                    )
                for env_beh, con_beh in env_con_behs:
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

    env_cond = env_cond.simplify()
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
            con_cond = con_cond_orig.simplify()
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
