from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.update import Update
from prop_lang.util import true, conjunct, neg, negate, conjunct_formula_set
from prop_lang.variable import Variable


class Transition:
    def __init__(
        self, src, condition: Formula, action: list[Update], output: list[Variable], tgt
    ):
        self.src = src
        self.condition = true() if condition is None else condition
        self.action = [] if action is None else action
        self.output = sorted(output, key=lambda x: str(x))
        self.tgt = tgt
        self.f = None
        self.pred_upgrades: list[BiOp] = []

    def __str__(self) -> str:
        to_str = lambda x: (
            str(x)
            if type(x) != tuple or type(x[1]) != frozenset
            else str(x[0]) + ", " + ", ".join(map(to_str, list(x[1])))
        )

        return (
            to_str(self.src)
            + " -> "
            + to_str(self.tgt)
            + " {"
            + str(self.condition)
            + " $ "
            + "; ".join([str(x) for x in self.action])
            + " >> "
            + "["
            + ", ".join([str(x) for x in self.output])
            + "]"
            + "}"
        )

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Transition):
            return (
                self.src == other.src
                and self.tgt == other.tgt
                and self.condition == other.condition
                and frozenset(self.action) == frozenset(other.action)
                and frozenset(self.output) == frozenset(other.output)
                and frozenset(self.pred_upgrades) == frozenset(other.pred_upgrades)
            )
        return NotImplemented

    def __hash__(self):
        return hash(
            (
                self.src,
                self.condition,
                frozenset(self.action),
                frozenset(self.output),
                self.tgt,
            )
        )

    def with_condition(self, new_condition):
        return Transition(self.src, new_condition, self.action, self.output, self.tgt)

    def from_to(self, new_src, new_tgt):
        return Transition(new_src, self.condition, self.action, self.output, new_tgt)

    def to(self, new_tgt):
        return Transition(self.src, self.condition, self.action, self.output, new_tgt)

    def add_condition(self, new_condition):
        return Transition(
            self.src,
            conjunct(self.condition, new_condition),
            self.action,
            self.output,
            self.tgt,
        )

    def complete_outputs(self, all_outputs):
        for o in all_outputs:
            if o not in self.output and negate(o) not in self.output:
                self.output.append(neg(o))
        return self

    def complete_action_set(self, vars):
        all_modified = []
        for act in self.action:
            all_modified.append(act.left)
        for v in vars:
            if v not in all_modified:
                self.action.append(Update(v, v))
        if len(self.action) != len(vars):
            raise Exception(
                "Error in action set completion:"
                + "vars "
                + ", ".join(map(str, vars))
                + "; trans: "
                + str(self)
            )
        return self

    def formula(self):
        if self.f is None:
            self.f = conjunct_formula_set(
                [self.condition.prev_rep()]
                + [BiOp(a.left, "=", a.right.prev_rep()) for a in self.action]
            )
        return self.f

    def set_predicate_upgrades(self, pred_upgrades: list[BiOp]):
        self.pred_upgrades = pred_upgrades

    def replace_formulas(self, context):
        t = self.with_condition(self.condition.replace_formulas(context))
        t.action = [a.replace_formulas(context) for a in self.action]
        return t
