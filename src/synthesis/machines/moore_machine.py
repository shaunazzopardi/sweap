from graphviz import Digraph
from prop_lang.formula import Formula
from prop_lang.util import (
    disjunct_formula_set,
    propagate_negations,
    label_pred,
    is_tautology,
    iff,
)
from synthesis.machines.machine import Machine


class MooreMachine(Machine):
    def __init__(
        self,
        name,
        init_index: int,
        env_events,
        con_events,
    ):
        self.name = name
        self.init_index = init_index
        self.init_st = {"st_" + str(init_index)}
        self.states = self.init_st
        self.env_events = env_events
        self.con_events = con_events
        self.transitions: dict[str, list[tuple[Formula, str]]] = {}
        self.prog_state = {}
        self.counter = -1
        self.out = {}

    def add_transitions(self, trans_dict: dict, symbol_table):
        intermed_trans = {}
        new_sts = {}
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            env_cond = env_behaviour.simplify()
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
                    intermed_trans[new_src] = []

            con_behaviour = disjunct_formula_set(
                trans_dict[(src_index, env_behaviour, tgt_index)]
            )
            con_cond = con_behaviour.simplify()
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

    def to_dot(self, pred_list: list[Formula] | None = None):
        to_replace = {}
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace[pred_var] = pred

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

        for src, beh_tgts in self.transitions.items():
            for beh, tgt in beh_tgts:
                label = str(beh.replace_vars(to_replace))
                dot.edge(str(src), str(tgt), label)

        return dot
