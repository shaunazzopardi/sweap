from graphviz import Digraph

import config
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
    propagate_negations,
    simplify_formula_without_math,
    sat,
    project_out_props,
    label_pred,
    is_tautology,
    iff,
)
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import (
    AbstractLTLSynthesisProblem,
)


class MooreMachine:
    def __init__(self, name, init_index: int, env_events, con_events, transitions={}):
        self.name = name
        self.init_index = init_index
        self.init_st = {"st_" + str(init_index)}
        self.states = self.init_st | transitions.keys()
        self.env_events = env_events
        self.con_events = con_events
        self.transitions = transitions
        self.prog_state = {}
        self.counter = -1
        self.out = {}

    def add_transitions(self, trans_dict: dict, symbol_table):
        intermed_trans = {}
        new_sts = {}
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            env_cond = (env_behaviour.simplify()).to_nuxmv()
            env_cond = propagate_negations(env_cond)

            new_src = "st_" + str(src_index)
            if new_src not in new_sts.keys():
                new_sts |= {new_src: [new_src]}
                self.transitions[new_src] = []
                self.out[new_src] = env_cond
                intermed_trans[new_src] = []
            else:
                if not is_tautology(iff(env_cond, self.out[new_src]), symbol_table):
                    new_new_src = new_src + "_" + str(len(new_sts[new_src]))
                    new_sts[new_src].append(new_new_src)
                    new_src = new_new_src
                    self.transitions[new_src] = []
                    self.out[new_src] = env_cond

            con_behaviour = disjunct_formula_set(
                trans_dict[(src_index, env_behaviour, tgt_index)]
            )
            con_cond = (con_behaviour.simplify()).to_nuxmv()
            con_cond = propagate_negations(con_cond)

            new_tgt = "st_" + str(tgt_index)

            intermed_trans[new_src] += [(con_cond, new_tgt)]

            self.states.add(new_src)
            self.states.add(new_tgt)

        for src, con_trans in intermed_trans.items():
            for con_cond, new_tgt in con_trans:
                if len(new_sts[new_tgt]) > 1:
                    for i in range(1, len(new_sts[new_tgt])):
                        self.transitions[src].append((con_cond, new_tgt + "_" + str(i)))
                    self.transitions[src].append((con_cond, new_tgt))
                else:
                    self.transitions[src].append((con_cond, new_tgt))

        for new_st in new_sts[list(self.init_st)[0]]:
            self.init_st.add(new_st)

    def __str__(self):
        return str(self.to_dot())

    def to_dot(self, pred_list: [Formula] = None):
        to_replace = []
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace += [BiOp(pred_var, ":=", pred)]

        dot = Digraph(
            name="MooreMachine",
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
            if s in self.out.keys():
                out = self.out[s]
                dot.node(str(s), str(out))
            else:
                dot.node(str(s))

        for s in self.init_st:
            dot.edge("init", str(s), style="solid")

        for src in self.transitions.keys():
            for beh, tgt in self.transitions.get(src):
                label = str(beh.replace_vars(to_replace))
                dot.edge(str(src), str(tgt), label)

        return dot

    def to_nuXmv_with_turns(
        self, prog_states, prog_out_events, state_pred_list, trans_pred_list
    ):
        state_pred_acts = [p.bool_var for p in state_pred_list]
        trans_pred_acts = [t for p in trans_pred_list for t in p.bool_rep.values()]
        pred_acts = state_pred_acts + trans_pred_acts

        dualise = config.Config.getConfig().dual
        guards_acts = {}

        init_cond = []
        for st in self.init_st:
            st_guard = self.out[st]
            init_cond.append(
                conjunct_formula_set(
                    [neg(Variable(stt)) for stt in self.states if stt != st]
                    + [Variable(st), st_guard]
                )
            )
        init_cond = disjunct_formula_set(init_cond)

        f = lambda x: (
            UniOp("next", x)
            if not dualise or (str(x).startswith("bin_") or x in pred_acts)
            else x
        )

        for src in self.transitions.keys():
            for con_beh, tgt in self.transitions.get(src):
                guard = "(turn = prog) & " + str(src) + " & " + str(con_beh)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()

                next_state = self.out[tgt].replace(f)

                act = conjunct_formula_set(
                    [
                        next_state,
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
