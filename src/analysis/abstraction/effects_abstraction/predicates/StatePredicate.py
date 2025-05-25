from analysis.abstraction.effects_abstraction.predicates.Predicate import (
    Predicate,
    refine_nexts,
)
from prop_lang.formula import Formula
from prop_lang.util import (
    neg,
    conjunct,
    sat,
    is_tautology,
    implies,
    iff,
    stringify_pred,
    X,
)
from prop_lang.variable import Variable


class StatePredicate(Predicate):
    def __init__(self, pred: Formula):
        self.pred = pred
        self.vars = pred.variablesin()
        self.options = [pred, neg(pred)]
        self.bool_var = stringify_pred(pred)
        self.neg_bool_var = neg(stringify_pred(pred))
        self.bool_rep = {
            self.pred: self.bool_var,
            neg(self.pred): self.neg_bool_var,
        }
        self.last_pre = {}
        self.last_post = {}

    def __str__(self):
        return str(self.pred)

    def __eq__(self, other):
        return isinstance(other, StatePredicate) and self.pred == other.pred

    def __hash__(self):
        return hash(self.pred)

    def variablesin(self):
        return self.vars

    def extend_effect_now(
        self, gu: Formula, old_effects: [(Formula, [Formula])], symbol_table
    ) -> [(Formula, [Formula])]:
        new_effects = []

        for now, nexts in old_effects:
            now_p = conjunct(now, self.pred)
            now_p_g = conjunct(gu, now_p.prev_rep())
            if sat(now_p_g, symbol_table):
                new_nexts = refine_nexts(now_p_g, nexts, symbol_table)
                if len(new_nexts) == 0:
                    raise Exception(
                        "Is this guard update formula unsatisfiable?\n" + str(gu)
                    )
                new_effects.append((now_p, new_nexts))
            else:
                now_neg_p = conjunct(now, neg(self.pred))
                now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
                new_nexts = refine_nexts(now_neg_p_g, nexts, symbol_table)
                if len(new_nexts) == 0:
                    raise Exception(
                        "Is this guard update formula unsatisfiable?\n" + str(gu)
                    )
                new_effects.append((now_neg_p, new_nexts))
                continue

            now_neg_p = conjunct(now, neg(self.pred))
            now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
            if sat(now_neg_p_g, symbol_table):
                new_nexts = refine_nexts(now_neg_p_g, nexts, symbol_table)
                if len(new_nexts) == 0:
                    raise Exception(
                        "Is this guard update formula unsatisfiable?\n" + str(gu)
                    )
                new_effects.append(
                    (now_neg_p, refine_nexts(now_neg_p_g, nexts, symbol_table))
                )

        return new_effects

    def extend_effect_next(
        self,
        gu: Formula,
        old_effects: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []
        for now, nexts in old_effects:
            new_nexts = self.refine_nexts_with_p(
                conjunct(gu, now.prev_rep()), nexts, symbol_table
            )
            new_effects.append((now, new_nexts))
        return new_effects

    def refine_nexts_with_p(self, now, nexts, symbol_table):
        new_nexts = []
        for next in nexts:
            next_p = conjunct(next, self.pred)
            if sat(conjunct(now, next_p), symbol_table):
                new_nexts.append(next_p)

            next_neg_p = conjunct(next, neg(self.pred))
            if sat(conjunct(now, next_neg_p), symbol_table):
                new_nexts.append(next_neg_p)
        return new_nexts

    def extend_effect(
        self, gu: Formula, old_effects: [(Formula, [Formula])], symbol_table
    ) -> [(Formula, [Formula])]:
        new_effects = []

        for now, nexts in old_effects:
            now_p = conjunct(now, self.pred)
            now_p_g = conjunct(gu, now_p.prev_rep())
            if sat(now_p_g, symbol_table):
                new_effects.append(
                    (
                        now_p,
                        self.refine_nexts_with_p(now_p_g, nexts, symbol_table),
                    )
                )
            else:
                now_neg_p = conjunct(now, neg(self.pred))
                now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
                new_effects.append(
                    (
                        now_neg_p,
                        self.refine_nexts_with_p(now_neg_p_g, nexts, symbol_table),
                    )
                )
                continue

            now_neg_p = conjunct(now, neg(self.pred))
            now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
            if sat(now_neg_p_g, symbol_table):
                new_effects.append(
                    (
                        now_neg_p,
                        self.refine_nexts_with_p(now_neg_p_g, nexts, symbol_table),
                    )
                )

        return new_effects

    # The below can help us keep now and next sets smaller
    def is_pre_cond(self, gu: Formula, symbol_table):
        if is_tautology(implies(gu, self.pred.prev_rep()), symbol_table):
            return self.bool_var
        else:
            neg_p = neg(self.pred)
            if is_tautology(implies(gu, neg_p.prev_rep()), symbol_table):
                return self.neg_bool_var

    def is_invar(self, gu: Formula, symbol_table):
        if is_tautology(
            implies(gu, iff(self.pred.prev_rep(), self.pred)), symbol_table
        ):
            return self.bool_var

    def is_post_cond(self, gu: Formula, symbol_table):
        if is_tautology(implies(gu, self.pred), symbol_table):
            self.last_post[gu] = self.bool_var
            return X(self.bool_var)
        else:
            neg_p = neg(self.pred)
            if is_tautology(implies(gu, neg_p), symbol_table):
                self.last_pre[gu] = self.bool_var
                return X(self.neg_bool_var)

    def boolean_rep(self):
        return self.bool_rep

    def to_smt(self, symbol_table):
        return self.pred.to_smt(symbol_table)
