from analysis.abstraction.effects_abstraction.predicates.Predicate import Predicate
from prop_lang.formula import Formula
from prop_lang.util import neg, conjunct, sat, is_tautology, implies, iff, stringify_pred, X
from prop_lang.variable import Variable


def refine_nexts(now, nexts, symbol_table):
    new_nexts = []
    for v, v_nexts in nexts:
        new_v_nexts = []
        # TODO optimisation: only itera.items()te over nexts of v if v is in cone of influence of v w.r.t. predicates in now and guard
        for v_next in v_nexts:
            if sat(conjunct(now, v_next), symbol_table):
                new_v_nexts.append(v_next)
        new_nexts.append((v, new_v_nexts))
    return new_nexts


class StatePredicate(Predicate):
    def __init__(self, pred: Formula):
        self.pred = pred
        self.vars = pred.variablesin()
        self.options = [pred, neg(pred)]
        self.bool_var = stringify_pred(pred)
        self.neg_bool_var = neg(stringify_pred(pred))
        self.bool_rep = {self.pred: self.bool_var, neg(self.pred): self.neg_bool_var}
        self.last_pre = {}
        self.last_post = {}

    def __eq__(self, other):
        return isinstance(other, StatePredicate) and self.pred == other.pred

    def __hash__(self):
        return hash(self.pred)

    def variablesin(self):
        return self.vars

    # TODO not sure this works, some nexts may be invalidated with new now?
    #  if pred has an update variable in it, then this will be caught when updating nexts
    #     what if it does not?
    #       e.g., if transition is true $ x := x + 1; nows are z == x + 1 and x == 1,
    #             given new predicate z == 0, we add it to nows,
    #             now, previously for when z == x + 1 is true, possible nexts are x == 1 and x != 1
    #             when we add z == 0, x != 1 next should become false, but we are not checking for it
    #             so ideally, for an exact abstraction, we should check that nexts still hold
    #              good: more exact abstraction, need for less future predicates -> smaller exponent
    #              bad: more smt checks, more time spent abstracting
    #             conclusion: good outweighs bad: better to have a more exact abstract,
    #                         and to reduce exponent (for synthesis purposes
    #             how likely is this situation to occur? depends on program, we are more likely to have things of the form
    #               z == x_prev + 1, but value of x_prev would be unknown
    #             optimisation: only check nexts if new predicate added has variables in the cone-of-influence
    #                           of the left hand side of the update
    def extend_effect_now(self,
                      gu: Formula,
                      old_effects: [(Formula, dict[Variable, [Formula]])],
                      symbol_table) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []

        for now, nexts in old_effects:
            now_p = conjunct(now, self.pred)
            now_p_g = conjunct(gu, now_p.prev_rep())
            if sat(now_p_g, symbol_table):
                new_effects.append((now_p, refine_nexts(now_p_g, nexts, symbol_table)))
            else:
                now_neg_p = conjunct(now, neg(self.pred))
                now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
                new_effects.append((now_neg_p, refine_nexts(now_neg_p_g, nexts, symbol_table)))
                continue

            now_neg_p = conjunct(now, neg(self.pred))
            now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
            if sat(now_neg_p_g, symbol_table):
                new_effects.append((now_neg_p, refine_nexts(now_neg_p_g, nexts, symbol_table)))

        return new_effects

    def extend_effect_next(self,
                      gu: Formula,
                      old_effects: [(Formula, dict[Variable, [Formula]])],
                      symbol_table) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []
        for now, nexts in old_effects:
            new_nexts = self.refine_nexts_with_p(conjunct(gu, now.prev_rep()), nexts, symbol_table)
            new_effects.append((now, new_nexts))
        return new_effects

    def refine_nexts_with_p(self, now, nexts, symbol_table):
        new_nexts = []
        for u, v_nexts in nexts:
            new_v_nexts = []
            # TODO may cause uneccessary repetition:
            #   should consider all updates relevant to self.vars together?
            #   or could this cause unnecessary explosion?
            #   e.g., for predicate x > y, and preds x > 1
            if u.left in self.vars:
                for v_next in v_nexts:
                    v_next_p = conjunct(v_next, self.pred)
                    if sat(conjunct(now, v_next_p), symbol_table):
                        new_v_nexts.append(v_next_p)
                    else:
                        v_next_neg_p = conjunct(v_next, neg(self.pred))
                        new_v_nexts.append(v_next_neg_p)
                        continue

                    v_next_neg_p = conjunct(v_next, neg(self.pred))
                    if sat(conjunct(now, v_next_neg_p), symbol_table):
                        new_v_nexts.append(v_next_neg_p)
                new_nexts.append((u, new_v_nexts))
            else:
                new_v_nexts.append((u, v_nexts))
        return new_nexts

    def extend_effect(self,
                      gu: Formula,
                      old_effects: [(Formula, dict[Variable, [Formula]])],
                      symbol_table) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []

        for now, nexts in old_effects:
            now_p = conjunct(now, self.pred)
            now_p_g = conjunct(gu, now_p.prev_rep())
            if sat(now_p_g, symbol_table):
                new_effects.append((now_p, self.refine_nexts_with_p(now_p_g, nexts, symbol_table)))
            else:
                now_neg_p = conjunct(now, neg(self.pred))
                now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
                new_effects.append((now_neg_p, self.refine_nexts_with_p(now_neg_p_g, nexts, symbol_table)))
                continue

            now_neg_p = conjunct(now, neg(self.pred))
            now_neg_p_g = conjunct(gu, now_neg_p.prev_rep())
            if sat(now_neg_p_g, symbol_table):
                new_effects.append((now_neg_p, self.refine_nexts_with_p(now_neg_p_g, nexts, symbol_table)))

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
        if is_tautology(implies(gu, iff(self.pred.prev_rep(), self.pred)), symbol_table):
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