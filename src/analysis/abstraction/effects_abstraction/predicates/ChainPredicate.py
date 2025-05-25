import itertools
from bisect import bisect_left

from analysis.abstraction.effects_abstraction.predicates.Predicate import (
    Predicate,
)
from programs.util import (
    binary_rep,
    add_prev_suffix,
    term_incremented_or_decremented,
)
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct,
    neg,
    sat,
    is_tautology,
    implies,
    disjunct_formula_set,
    X,
    G,
    F,
    disjunct,
    stringify_term,
    conjunct_formula_set,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


def p_or_dict_val(ps, d):
    new_val = []
    for p in ps:
        if p not in d.keys():
            new_val.append(p)
        else:
            new_val.extend(d[p])
    return new_val


def old_preds_to_new(new_i, chain):
    chain_length = len(chain)
    new_pred = chain[new_i]
    if chain_length == 1:
        return [new_pred, neg(new_pred)]
    if new_i == 0:
        old_first = chain[1]
        return {old_first: [new_pred, conjunct(neg(new_pred), old_first)]}
    elif new_i == chain_length - 1:
        old_last = chain[new_i - 1]
        return {neg(old_last): [conjunct(neg(old_last), new_pred), neg(new_pred)]}
    else:
        old_i = chain[new_i + 1]
        old_i_minus_1 = chain[new_i - 1]
        return {
            conjunct(neg(old_i_minus_1), old_i): [
                conjunct(neg(old_i_minus_1), new_pred),
                conjunct(neg(new_pred), old_i),
            ]
        }


def recheck_nexts(prev_state, nexts, symbol_table):
    return [
        v_next for v_next in nexts if sat(conjunct(prev_state, v_next), symbol_table)
    ]


class ChainPredicate(Predicate):
    def __init__(self, term: Formula, program, accelerate=False):
        # TODO this is class is no longer updating correctly;
        #  if term is over multiple variables, then updates need to be partitioned according to vars appearing in term
        #
        self.program = program
        self.raw_state_preds = []
        self.tran_preds = []
        self.bottom_ranking = None
        self.top_ranking = None
        self.term = term
        self.vars = term.variablesin()
        self.chain = []  # this will be a mutually exclusive list of predicates
        self.old_to_new = (
            {}
        )  # this will be a map from previous values of self.chain to new values of self.chain
        self.unmodified = set()
        self.pred_to_chain = {}
        self.bin_vars = []
        self.bin_rep = {}
        self.single_pred_bin_rep = {}

        self.last_pre = {}
        self.last_post = {}
        self.init_now = set()
        self.init_next = set()

        self.accelerate = accelerate

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, ChainPredicate):
            return self.term == other.term
        return NotImplemented

    def __hash__(self):
        return hash(self.term)

    def variablesin(self):
        return self.vars

    def add_predicate(self, preds):
        # assuming each predicate only has var as a variable
        if len(preds) == 0:
            self.old_to_new_pos = None
            return

        old_to_new_pos = None
        for p in preds:
            i = bisect_left(
                self.raw_state_preds,
                float(str(p.right)),
                key=lambda x: float(str(x.right)),
            )
            # this rearranges x < 0 and x <= 0 predicates, so that they are in order of strength
            if p.op == "<":
                if 0 < i < len(self.raw_state_preds):
                    if self.raw_state_preds[i - 1].right == p.right:
                        i = i - 1
            elif p.op == "<=":
                if (
                    len(self.raw_state_preds) > 0
                    and i < len(self.raw_state_preds)
                    and self.raw_state_preds[i].right == p.right
                ):
                    i = i + 1

            self.raw_state_preds.insert(i, p)
            if old_to_new_pos is None or isinstance(old_to_new_pos, list):
                old_to_new_pos = old_preds_to_new(i, self.raw_state_preds)
            else:
                int_old_to_new_pos = old_preds_to_new(i, self.raw_state_preds)
                old_to_new_pos = {
                    old_p: p_or_dict_val(ps, int_old_to_new_pos)
                    for old_p, ps in old_to_new_pos.items()
                }
                old_to_new_pos |= {
                    old_p: ps
                    for old_p, ps in int_old_to_new_pos.items()
                    if old_p in self.chain and old_p not in old_to_new_pos.keys()
                }

        self.old_to_new = old_to_new_pos

        new_chain = []
        self.pred_to_chain = {}
        for i, p in enumerate(self.raw_state_preds):
            if i == 0:
                new_chain.append(p)
            else:
                all_before_neg = conjunct(neg(self.raw_state_preds[i - 1]), p)
                new_chain.append(all_before_neg)
            self.pred_to_chain[p] = self.chain

        new_chain.append(neg(self.raw_state_preds[-1]))

        if len(self.chain) == 0:
            self.chain = new_chain
            if self.accelerate:
                self.init_ranking_refinement()
        else:
            if self.accelerate:
                if self.chain[0] != new_chain[0] and self.bottom_ranking is not None:
                    self.bottom_ranking = self.bottom_ranking.replace_formulas(
                        {self.chain[0]: new_chain[0]}
                    )

                if self.chain[-1] != new_chain[-1] and self.top_ranking is not None:
                    self.top_ranking = self.top_ranking.replace_formulas(
                        {self.chain[-1]: new_chain[-1]}
                    )

            self.chain = new_chain

        for i, p in enumerate(self.raw_state_preds):
            self.pred_to_chain[neg(p)] = self.chain[i + 1 :]

        self.bin_vars, self.bin_rep = binary_rep(
            self.chain, "bin_" + stringify_term(self.term)
        )

        for i, f in enumerate(self.chain):
            if i + 1 < len(self.chain):
                # TODO for v = 8, we have a big representation, when !(v <= 7) && v <= 8 suffices
                if i < len(self.chain) / 2:
                    if i != 0:
                        self.single_pred_bin_rep[self.raw_state_preds[i]] = (
                            disjunct_formula_set(
                                [self.bin_rep[p] for p in self.chain[0 : i + 1]]
                            )
                        )
                    if i < len(self.raw_state_preds):
                        self.single_pred_bin_rep[neg(self.raw_state_preds[i])] = (
                            conjunct_formula_set(
                                [neg(self.bin_rep[p]) for p in self.chain[0 : i + 1]]
                            )
                        )
                else:
                    if i != 0:
                        self.single_pred_bin_rep[self.raw_state_preds[i]] = (
                            conjunct_formula_set(
                                [neg(self.bin_rep[p]) for p in self.chain[i + 1 :]]
                            )
                        )
                    if i < len(self.raw_state_preds):
                        self.single_pred_bin_rep[neg(self.raw_state_preds[i])] = (
                            disjunct_formula_set(
                                [self.bin_rep[p] for p in self.chain[i + 1 :]]
                            )
                        )

    def refine_and_rename_nexts(self, gu, prev_state, nexts, symbol_table):
        new_nexts = []
        for old_next in nexts:
            for next in self.replace_formulas_multiple_but(
                self.old_to_new, old_next, gu, False
            ):
                if sat(conjunct(prev_state, next), symbol_table):
                    new_nexts.append(next)
        return new_nexts

    def replace_formulas_multiple_but(self, old_to_new, f, gu, now_or_next):
        if (now_or_next and gu not in self.init_now) or (
            not now_or_next and gu not in self.init_next
        ):
            if isinstance(f, Value):
                return self.chain
            else:
                return [conjunct(f, p) for p in self.chain]
        else:
            if isinstance(old_to_new, list):
                return [conjunct(f, p) for p in self.chain]
                # raise Exception("replace_formulas_multiple_but: Unexpectedly old_to_new is of type list.")
            modified = set(itertools.chain.from_iterable(old_to_new.values()))

            return f.replace_formulas_multiple(
                old_to_new | {p: [p] for p in self.chain if p not in modified}
            )

    def extend_effect(
        self,
        gu: Formula,
        old_effects: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []
        for old_now, nexts in old_effects:
            new_nows = self.replace_formulas_multiple_but(
                self.old_to_new, old_now, gu, True
            )
            for new_now in new_nows:
                prev_state = conjunct(gu, new_now.prev_rep())
                if sat(prev_state, symbol_table):
                    new_nexts = self.refine_and_rename_nexts(
                        gu, prev_state, nexts, symbol_table
                    )
                    if len(new_nexts) > 0:
                        new_effects.append((new_now, new_nexts))
                    else:
                        raise Exception(
                            "Is this guard update formula unsatisfiable?\n" + str(gu)
                        )

        return new_effects

    def extend_effect_now(
        self,
        gu: Formula,
        old_effects: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []
        for old_now, nexts in old_effects:
            new_nows = self.replace_formulas_multiple_but(
                self.old_to_new, old_now, gu, True
            )
            for new_now in new_nows:
                prev_state = conjunct(gu, new_now.prev_rep())
                if sat(prev_state, symbol_table):
                    if len(nexts) == 0:
                        new_effects.append((new_now, nexts))
                    else:
                        new_nexts = recheck_nexts(prev_state, nexts, symbol_table)
                        if len(new_nexts) > 0:
                            new_effects.append((new_now, new_nexts))
                        else:
                            raise Exception("Is gu unsatisfiable? " + str(gu))

        return new_effects

    def extend_effect_next(
        self,
        gu: Formula,
        old_effects: [(Formula, dict[Variable, [Formula]])],
        symbol_table,
    ) -> [(Formula, dict[Variable, [Formula]])]:
        new_effects = []
        for now, nexts in old_effects:
            new_nexts = self.refine_and_rename_nexts(
                gu, conjunct(gu, now.prev_rep()), nexts, symbol_table
            )
            new_effects.append((now, new_nexts))

        return new_effects

    def is_pre_cond(self, gu: Formula, symbol_table):
        nope = False
        pre = None
        for p in self.chain:
            if is_tautology(implies(gu, p.prev_rep()), symbol_table):
                if nope:
                    return None
                nope = True
                pre = p

        if pre is not None:
            self.last_pre[gu] = pre
        return pre

    def is_invar(self, gu: Formula, symbol_table):
        if is_tautology(
            implies(gu, BiOp(self.term, "=", self.term.prev_rep())),
            symbol_table,
        ):
            return self

    def is_post_cond(self, gu: Formula, symbol_table):
        nope = False
        post = None
        for p in self.chain:
            if is_tautology(implies(gu, p), symbol_table):
                if nope:
                    return None
                nope = True
                post = X(p)

        if post is not None:
            self.last_post[gu] = post
        return post

    def refine_old_pre_cond(self, f, gu: Formula, symbol_table):
        p = f
        # need to check that self.old_to_new is dict because when turning of parallelisation, and a transition with the
        # same gu could have been processed already
        if isinstance(self.old_to_new, dict) and p in self.old_to_new.keys():
            for new_p in self.old_to_new[p]:
                if is_tautology(implies(gu, new_p.prev_rep()), symbol_table):
                    return new_p, self
            return None, self
        else:
            return f, self

    def refine_old_post_cond(self, f, gu: Formula, symbol_table):
        if isinstance(f, UniOp) and f.op == "X":
            p = f.right
        else:
            raise Exception("refine_old_post_cond called with " + str(f))
        # need to check that self.old_to_new is dict because when turning of parallelisation, and a transition with the
        # same gu could have been processed already
        if isinstance(self.old_to_new, dict) and p in self.old_to_new.keys():
            for new_p in self.old_to_new[p]:
                if is_tautology(implies(gu, new_p), symbol_table):
                    return X(new_p), self
            return None, self
        else:
            return f, self

    def boolean_rep(self):
        return self.single_pred_bin_rep | self.bin_rep

    def init_ranking_refinement(self):
        (
            only_updated_by_constants,
            there_is_dec,
            there_is_inc,
        ) = term_incremented_or_decremented(self.program, self.term)

        if not only_updated_by_constants:
            if there_is_dec:
                dec = BiOp(self.term, "<", add_prev_suffix(self.term))
                self.tran_preds.append(dec)
                if there_is_inc:
                    inc = BiOp(add_prev_suffix(self.term), "<", self.term)
                    self.tran_preds.append(inc)
                    self.bottom_ranking = implies(
                        G(F(dec)), G(F(disjunct(inc, self.chain[0])))
                    )
                    self.top_ranking = implies(
                        G(F(inc)), G(F(disjunct(dec, self.chain[-1])))
                    )
                else:
                    self.bottom_ranking = implies(G(F(dec)), G(F(self.chain[0])))
            elif there_is_inc:
                inc = BiOp(add_prev_suffix(self.term), "<", self.term)
                self.tran_preds.append(inc)
                self.top_ranking = implies(G(F(inc)), G(F(self.chain[-1])))
