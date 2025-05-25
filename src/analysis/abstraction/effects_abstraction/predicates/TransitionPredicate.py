from abc import ABC

from analysis.abstraction.effects_abstraction.predicates.Predicate import (
    Predicate,
    refine_nexts,
)
from prop_lang.formula import Formula
from prop_lang.util import (
    neg,
    stringify_pred,
    conjunct,
    sat,
    is_tautology,
    implies,
    X,
    conjunct_formula_set,
    iff,
)


class TransitionPredicate(Predicate, ABC):
    def __init__(self, tran_preds: [Formula]):
        self.preds = tran_preds
        self.vars = tran_preds[0].variablesin()
        self.stutter = conjunct_formula_set([neg(t) for t in tran_preds])
        self.options = [
            conjunct_formula_set([t] + [neg(tt) for tt in tran_preds if t != tt])
            for t in tran_preds
        ] + [self.stutter]
        self.bool_rep = {t: stringify_pred(t) for t in tran_preds}

    def __str__(self):
        return ", ".join(map(str, self.preds))

    def __eq__(self, other):
        return isinstance(other, TransitionPredicate) and str(self) == str(other)

    def __hash__(self):
        return hash(str(self))

    def variablesin(self):
        return self.vars

    def extend_effect_next(
        self, gu: Formula, old_effects: [(Formula, [Formula])], symbol_table
    ) -> [(Formula, [Formula])]:
        new_effects = []
        for now, nexts in old_effects:
            new_nexts = self.refine_nexts_with_p(
                conjunct(gu, now.prev_rep()), nexts, symbol_table
            )
            if len(new_nexts) == 0:
                raise Exception(
                    "Is this guard update formula unsatisfiable?\n" + str(gu)
                )
            new_effects.append((now, new_nexts))
        return new_effects

    def refine_nexts_with_p(self, now, nexts, symbol_table):
        new_nexts = []
        for v_next in nexts:
            for option in self.options:
                v_next_p = conjunct(v_next, option)
                if sat(conjunct(now, v_next_p), symbol_table):
                    new_nexts.append(v_next_p)
        return new_nexts

    def is_post_cond(self, gu: Formula, symbol_table):
        for option in self.options:
            if is_tautology(implies(gu, option), symbol_table):
                return X(option.replace_formulas(self.bool_rep))

    def boolean_rep(self):
        return self.bool_rep

    def to_smt(self, symbol_table):
        return self.pred.to_smt(symbol_table)

    def extend_effect(
        self, gu: Formula, old_effects: [(Formula, [Formula])], symbol_table
    ) -> [(Formula, [Formula])]:
        new_effects = []

        for now, nexts in old_effects:
            for option in self.options:
                now_p = conjunct(now, option)
                now_p_g = conjunct(gu, now_p.prev_rep())
                if sat(now_p_g, symbol_table):
                    new_nexts = self.refine_nexts_with_p(now_p_g, nexts, symbol_table)
                    if len(new_nexts) == 0:
                        raise Exception(
                            "Is this guard update formula unsatisfiable?\n" + str(gu)
                        )

                    new_effects.append((now_p, new_nexts))

        return new_effects

    def extend_effect_now(
        self, gu: Formula, old_effects: [(Formula, [Formula])], symbol_table
    ) -> [(Formula, [Formula])]:
        new_effects = []

        for now, nexts in old_effects:
            for option in self.options:
                now_p = conjunct(now, option)
                now_p_g = conjunct(gu, now_p.prev_rep())
                if sat(now_p_g, symbol_table):
                    new_nexts = refine_nexts(now_p_g, nexts, symbol_table)
                    if len(new_nexts) == 0:
                        raise Exception(
                            "Is this guard update formula unsatisfiable?\n" + str(gu)
                        )

                    new_effects.append((now_p, new_nexts))

        return new_effects

    def is_pre_cond(self, gu: Formula, symbol_table):
        for option in self.options:
            if is_tautology(implies(gu, option.prev_rep()), symbol_table):
                return option.replace_formulas(self.bool_rep)

    def is_invar(self, gu: Formula, symbol_table):
        for option in self.options:
            if is_tautology(implies(gu, iff(option.prev_rep(), option)), symbol_table):
                return option.replace_formulas(self.bool_rep)
