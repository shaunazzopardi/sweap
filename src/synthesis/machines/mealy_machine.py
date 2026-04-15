from graphviz import Digraph
from prop_lang.util import (
    disjunct_formula_set,
    propagate_negations,
    label_pred,
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
