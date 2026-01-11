import itertools
import logging
import time
from multiprocessing import Pool

from pysmt.shortcuts import Symbol, Exists, And
from pysmt.typing import INT
from analysis.smt_checker import quantifier_elimination

import config
from analysis.abstraction.effects_abstraction.abs_util import (
    update_var_partition_mult,
)
from analysis.abstraction.effects_abstraction.predicates import StatePredicate
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import (
    ChainPredicate,
)
from analysis.abstraction.effects_abstraction.predicates.Predicate import (
    Predicate,
)
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.abstraction.effects_abstraction.predicates.TransitionPredicate import (
    TransitionPredicate,
)
from analysis.abstraction.interface.predicate_abstraction import (
    PredicateAbstraction,
)
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import MathRels
from prop_lang.types.types import BOOLEAN
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct,
    massage_ltl_for_dual,
    neg,
    conjunct_formula_set,
    conjunct_typed_valuation_set,
    disjunct_formula_set,
    true,
    sat,
    X,
    iff,
    strip_mathexpr,
    propagate_nexts,
    is_tautology,
    all_sat_models,
    fnode_to_formula,
    atomic_predicates,
    normalise_pred_multiple_vars, implies,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

logger = logging.getLogger(__name__)


class EffectsAbstraction(PredicateAbstraction):
    def get_interpolants(self) -> list[Formula]:
        raise NotImplementedError

    def __init__(self, program: Program, old_to_new_st_preds):
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_ltl = {}
        self.input_preds = []
        self.input_models = []

        vars = [
            Variable(v) for v in program.symbol_table.keys() if "_prev_prev" not in v
        ]
        self.partitions = {i: {v} for i, v in enumerate(vars)}
        self.v_to_p = {v: set() for v in vars}
        self.v_to_partition = {v: i for i, v in enumerate(vars)}

        self.t_partitions = {}
        self.t_v_to_p = {}
        self.t_v_to_partition = {}

        self.t_ignore_in_nows = {}
        self.t_ignore_in_nexts = {}

        self.t_u_to_curr_u = {}
        self.t_us_part = {}
        self.t_us_part_to_pred = {}

        self.v_to_chain_pred = {}

        self.init_conf: Formula = true()
        self.init_state_abstraction = [[true()]]
        self.init_constants = []

        self.init_program_trans = None
        self.non_init_program_trans = None

        self.init_program_gus = None
        self.non_init_program_gus = None
        self.gu_to_trans = {}

        self.state_predicates = set()
        self.raw_state_predicates = set()
        self.transition_predicates = set()
        self.raw_transition_predicates = set()
        self.chain_rep = {}

        self.current_chain_all_bin_rep = {}
        self.pred_to_v = {}

        self.ranking_constraints = {}
        self.structural_loop_constraints = []
        self.loops = []
        self.var_relabellings = {}

        self.program = program
        self.loop_vars = set()
        self.loop_counter = 0
        self.sat_input_models = []

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions(old_to_new_st_preds)

        self.symbol_table = {v: t for v, t in program.symbol_table.items()}

    def abstract_program_transitions(self, old_to_new_st_preds):
        orig_transitions, stutter = (
            self.program.orig_ts,
            self.program.stutter_ts,
        )

        self.init_program_trans = []

        all_trans = [
            t.with_condition(t.condition.replace_formulas(old_to_new_st_preds))
            for t in orig_transitions + stutter
        ]
        self.init_conf = conjunct_typed_valuation_set(self.program.init_var_values)
        self.init_program_trans = {
            t
            for t in all_trans
            if t.src == self.program.initial_state
            and sat(
                conjunct(self.init_conf.prev_rep(), t.formula()),
                self.program.symbol_table,
            )
        }

        self.init_program_gus = {t.formula() for t in self.init_program_trans}
        self.init_program_gus_to_t = {t.formula(): t for t in self.init_program_trans}

        self.non_init_program_trans = all_trans
        self.non_init_program_gus = {t.formula() for t in self.non_init_program_trans}

        for t in self.non_init_program_trans:
            gu = t.formula()
            if gu in self.gu_to_trans.keys():
                self.gu_to_trans[gu].append(t)
            else:
                self.gu_to_trans[gu] = [t]

        for gu in self.non_init_program_gus | self.init_program_gus:
            self.abstract_effect_ltl[gu] = true()
            self.abstract_effect_invars[gu] = set()
            self.abstract_effect_constant[gu] = set()

            t = self.gu_to_trans[gu][0]
            self.t_u_to_curr_u[gu] = {a: frozenset({a}) for a in t.action}
            parts = self.t_u_to_curr_u[gu].values()
            self.t_ignore_in_nows[gu] = set()
            self.t_ignore_in_nexts[gu] = set()
            self.t_us_part[gu] = [part for part in parts]
            self.t_us_part_to_pred[gu] = {part: (set(), set()) for part in parts}
            empty_effects = {part: [(true(), [true()])] for part in parts}
            self.abstract_effect[gu] = empty_effects

    def add_predicates(
        self,
        new_state_predicates: [Formula],
        new_transition_predicates: [Formula],
        signatures,
        parallelise=True,
    ):

        self.add_state_predicates(
            new_state_predicates | new_transition_predicates, signatures, parallelise
        )

    def add_ranking_constraints(
        self, new_ranking_constraints: dict[Formula, list[Formula]]
    ):
        for dec, constraint in new_ranking_constraints:
            processed_ltl_constraints = []
            processed = strip_mathexpr(constraint.right)
            processed_ltl_constraints.append(processed)
            processed_dec = self.var_relabellings[dec]
            if processed_dec not in self.ranking_constraints.keys():
                self.ranking_constraints[processed_dec] = processed_ltl_constraints
            else:
                self.ranking_constraints[processed_dec].extend(
                    processed_ltl_constraints
                )

    def add_structural_loop_constraints(
        self, in_loop_vars, new_structural_loop_constraints
    ):
        self.symbol_table.update({str(v): BOOLEAN for v in in_loop_vars})
        self.loop_vars.update(in_loop_vars)
        for constraint in new_structural_loop_constraints:
            processed_ltl_constraints = []
            processed = strip_mathexpr(constraint)
            processed_ltl_constraints.append(processed)
            self.structural_loop_constraints.extend(processed_ltl_constraints)

    def process_preds(self, new_state_predicates: list[Formula]):
        use_chain_preds = not config.Config.getConfig().no_binary_enc
        remaining_st_preds = list(new_state_predicates)

        # pred_only_contains_input_vars = lambda x: (
        #     True
        #     if not any(v for v in x.variablesin() if v in self.program.local_vars)
        #     else False
        # )

        new_preds = set()

        accelerate = config.Config.getConfig().eager_fairness

        if use_chain_preds:
            term_to_p_for_chain = {}
            remaining_st_preds = []
            for p in new_state_predicates:
                if isinstance(p, BiOp) and (p.op == MathRels.LT or p.op == MathRels.LE):
                    if p.left not in term_to_p_for_chain.keys():
                        term_to_p_for_chain[p.left] = [p]
                    else:
                        term_to_p_for_chain[p.left].append(p)
                else:
                    f_p = StatePredicate(p, self.has_input_vars(p))
                    self.raw_state_predicates.add(p)
                    remaining_st_preds.append(f_p)
                    new_preds.add(f_p)
                    self.state_predicates.add(f_p)
                    self.var_relabellings.update(f_p.boolean_rep())

            for term, preds in term_to_p_for_chain.items():
                self.raw_state_predicates.update(preds)
                new_chain_pred = False
                if term not in self.v_to_chain_pred.keys():
                    v_chain_pred = ChainPredicate(
                        term,
                        self.program,
                        self.has_input_vars(term),
                        accelerate,
                    )
                    self.v_to_chain_pred[term] = v_chain_pred
                    new_chain_pred = True
                else:
                    v_chain_pred = self.v_to_chain_pred[term]

                v_chain_pred.add_predicate(preds)

                self.symbol_table |= {str(b): BOOLEAN for b in v_chain_pred.bin_vars}

                if new_chain_pred and accelerate and len(v_chain_pred.tran_preds) > 0:
                    gu = TransitionPredicate(
                        v_chain_pred.tran_preds, v_chain_pred.is_input
                    )
                    new_preds.add(gu)
                    self.transition_predicates.add(gu)
                    self.raw_transition_predicates.update(v_chain_pred.tran_preds)
                    self.var_relabellings.update(gu.boolean_rep())
                    remaining_st_preds.append(gu)
                new_preds.add(v_chain_pred)

                self.var_relabellings.update(v_chain_pred.boolean_rep())

                if new_chain_pred:
                    new_init_abs = []
                    for p in v_chain_pred.chain:
                        for m in self.init_state_abstraction:
                            m_with_p = (
                                m + [p]
                                if len(m) > 0
                                and not (isinstance(m[0], Value) and m[0].is_true())
                                else [p]
                            )
                            if sat(
                                conjunct_formula_set(m_with_p + [self.init_conf]),
                                self.symbol_table,
                            ):
                                new_init_abs.append(m_with_p)
                    self.init_state_abstraction = new_init_abs
                else:
                    old_to_new = v_chain_pred.old_to_new
                    # TODO if transition pred do not update
                    new_init_abs = []
                    for m in self.init_state_abstraction:
                        no_old_p = True
                        for old_p in old_to_new.keys():
                            if old_p in m:
                                no_old_p = False
                                new_m = [_p for _p in m if _p != old_p]
                                for p in old_to_new[old_p]:
                                    m_with_p = new_m + [p]
                                    if sat(
                                        conjunct_formula_set(
                                            m_with_p + [self.init_conf]
                                        ),
                                        self.symbol_table,
                                    ):
                                        new_init_abs.append(m_with_p)
                        if no_old_p:
                            new_init_abs.append(m)
                    self.init_state_abstraction = new_init_abs
                    # TODO: to avoid having to learn init values, re-introduce second state abstraction
                    #       do it for each model? second_state_abs: dom(init_state_abs) -> [[preds]]
                    #       maybe this is a bit too much
        else:
            for p in remaining_st_preds:
                f_p = StatePredicate(p, self.has_input_vars(p))
                new_preds.add(f_p)
                self.state_predicates.add(f_p)
                self.var_relabellings.update(f_p.boolean_rep())
            remaining_st_preds = new_preds
        # TODO: this is also considering control state variables, exclude these
        (
            self.partitions,
            self.v_to_p,
            self.v_to_partition,
        ) = update_var_partition_mult(
            new_preds, self.partitions, self.v_to_p, self.v_to_partition
        )

        for p in remaining_st_preds:
            self.var_relabellings |= p.boolean_rep()

            if isinstance(p, TransitionPredicate):
                self.symbol_table.update(
                    {str(bool_var): BOOLEAN for bool_var in p.bool_rep.values()}
                )

                if not p.is_input:
                    self.init_constants.append(p.stutter)
            else:
                # For structural refinement we treat transition predicates as state predicates
                self.symbol_table.update({str(p.bool_var): BOOLEAN})
                if p.is_input:
                    continue
                if "_prev" in str(p):
                    if is_tautology(
                        implies(
                            conjunct_formula_set(
                                [
                                    BiOp(v, "=", v.prev_rep())
                                    for v in self.program.local_vars
                                ]
                            ),
                            p.pred,
                        ),
                        self.symbol_table,
                    ):
                        self.init_constants.append(p.pred)
                    else:
                        self.init_constants.append(neg(p.pred))
                else:
                    new_init_abs = []
                    for m in self.init_state_abstraction:
                        for choice in p.choices():
                            m_with_p = m + [choice]
                            if sat(
                                conjunct_formula_set(m_with_p + [self.init_conf]),
                                self.symbol_table,
                            ):
                                new_init_abs.append(m_with_p)
                    if len(new_init_abs) == 0:
                        print("")
                    self.init_state_abstraction = new_init_abs

        return new_preds

    def has_input_vars(self, x):
        return any(v for v in x.variablesin() if v in self.program.num_in_out)

    def add_state_predicates(
        self, new_state_predicates: list[Formula], signatures, parallelise=True
    ):
        if len(new_state_predicates) == 0:
            return
        new_state_predicates = sorted(new_state_predicates, key=lambda p: str(p))
        # assuming input state predicates have been normalised (all of type < or <=, and vars on LHS and constants on RHS)

        logger.info("Adding predicates to predicate abstraction:")
        logger.info(
            "state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]"
        )

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()

        new_preds = self.process_preds(new_state_predicates)

        no_of_workers = config.Config.getConfig().workers if parallelise else 1

        all_preds = self.state_predicates | set(self.v_to_chain_pred.values())

        # new_preds = list(new_preds)
        # # we do this sorting to ensure deterministic behaviour in abstraction, in case of bugs
        # new_preds.sort(key=lambda x: str(x))

        # TODO: do below incrementally
        self.input_preds = []
        for c in self.v_to_chain_pred.values():
            if self.has_input_vars(c):
                self.input_preds.append(c)

        for c in self.state_predicates:
            if self.has_input_vars(c):
                self.input_preds.append(c)
        for c in self.transition_predicates:
            if self.has_input_vars(c):
                self.input_preds.append(c)

        if len(self.input_preds) > 0:
            new_qe_preds = set()
            self.input_models = all_sat_models(
                self.input_preds, self.program.symbol_table
            )
            new_models = []
            for m in self.input_models:
                exist_vars = [Symbol(str(v), INT) for v in self.program.num_in_out]
                quant_formula = Exists(
                    exist_vars,
                    And(*m.to_smt(self.program.symbol_table)),
                )

                ret = quantifier_elimination(quant_formula)
                rett = fnode_to_formula(ret)
                normalised_state_preds = set()
                if len(rett.variablesin()) > 0:
                    old_to_new = {}
                    for p in atomic_predicates(rett):
                        if len(p.variablesin()) == 0:
                            continue
                        result = normalise_pred_multiple_vars(
                            p, signatures, self.symbol_table
                        )
                        if isinstance(result, Variable):
                            normalised_state_preds.add(result)
                        else:
                            sig, new_p, preds = result
                            old_to_new[p] = new_p
                            signatures.add(sig)
                            normalised_state_preds.update(preds)
                    new_qe_preds.update(
                        {
                            p
                            for p in normalised_state_preds
                            if p not in self.raw_state_predicates
                        }
                    )
                    new_models.append(conjunct(rett.replace_formulas(old_to_new), m))
                else:
                    new_models.append(m)

            self.sat_input_models = new_models
            print("Adding preds for input models: " + ", ".join(map(str, new_qe_preds)))
            new_new_preds = self.process_preds(new_qe_preds)
            new_preds.update(new_new_preds)

        gus = []
        gu_invars = []
        gu_constants = []
        configs = []
        dual_env_props = []
        gu_effects = []
        all_predss = []
        new_predss = []
        partitions = []
        v_to_preds = []
        v_to_partitions = []
        u_to_curr_us = []
        us_parts = []
        us_part_to_preds = []
        ignore_in_nows = []
        ignore_in_nexts = []
        relabelling = []
        symbol_tables = []
        for gu in self.non_init_program_gus | self.init_program_gus:
            gus.append(gu)
            gu_invars.append(self.abstract_effect_invars[gu])
            gu_constants.append(self.abstract_effect_constant[gu])
            configs.append(config.Config.getConfig())
            dual_env_props.append([v for v, _ in self.program.env_events])
            gu_effects.append(self.abstract_effect[gu])
            all_predss.append(all_preds)
            new_predss.append(new_preds)
            partitions.append(self.partitions)
            v_to_preds.append(self.v_to_p)
            v_to_partitions.append(self.v_to_partition)
            u_to_curr_us.append(self.t_u_to_curr_u[gu])
            us_parts.append(self.t_us_part[gu])
            us_part_to_preds.append(self.t_us_part_to_pred[gu])
            ignore_in_nows.append(self.t_ignore_in_nows[gu])
            ignore_in_nexts.append(self.t_ignore_in_nexts[gu])
            relabelling.append(self.var_relabellings)
            symbol_tables.append(self.symbol_table)
        with Pool(no_of_workers) as pool:
            results = pool.map(
                compute_abstract_effect_for_guard_update,
                zip(
                    gus,
                    gu_invars,
                    gu_constants,
                    configs,
                    dual_env_props,
                    gu_effects,
                    all_predss,
                    new_predss,
                    partitions,
                    v_to_preds,
                    v_to_partitions,
                    u_to_curr_us,
                    us_parts,
                    us_part_to_preds,
                    ignore_in_nows,
                    ignore_in_nexts,
                    relabelling,
                    symbol_tables,
                ),
            )

        for (
            gu,
            invars,
            constants,
            new_effects,
            new_u_to_curr_u,
            new_us_part,
            new_us_part_to_pred,
            bookkeeping,
            new_ignore_in_nows,
            new_ignore_in_nexts,
            gu_ltl,
        ) in results:
            (init_nows, init_nexts, pres, posts) = bookkeeping
            self.t_ignore_in_nows[gu] = new_ignore_in_nows
            self.t_ignore_in_nexts[gu] = new_ignore_in_nexts

            for p in init_nows:
                if isinstance(p, ChainPredicate):
                    actual_p = self.v_to_chain_pred[p.term]
                    actual_p.init_now.add(gu)
            for p in init_nexts:
                if isinstance(p, ChainPredicate):
                    actual_p = self.v_to_chain_pred[p.term]
                    actual_p.init_next.add(gu)
            for p in new_preds:
                if isinstance(p, ChainPredicate):
                    actual_p = self.v_to_chain_pred[p.term]
                    if p not in pres.keys() and gu in actual_p.last_pre.keys():
                        actual_p.last_pre.pop(gu)
                    if p not in posts.keys() and gu in actual_p.last_post.keys():
                        actual_p.last_post.pop(gu)

            for p, pre in pres.items():
                if isinstance(p, ChainPredicate):
                    actual_p = self.v_to_chain_pred[p.term]
                    if gu in p.last_pre.keys():
                        if p.last_pre[gu] in constants:
                            constants.remove(p.last_pre[gu])
                    actual_p.last_pre.update({gu: pre})
                constants.add(pre)
            for p, post in posts.items():
                if isinstance(p, ChainPredicate):
                    actual_p = self.v_to_chain_pred[p.term]
                    if gu in p.last_post.keys():
                        if p.last_post[gu] in constants:
                            constants.remove(p.last_post[gu])
                    actual_p.last_post.update({gu: post})
                constants.add(post)

            self.abstract_effect_invars[gu] = {
                p for p in invars if not isinstance(p, ChainPredicate)
            }
            self.abstract_effect_invars[gu].update(
                {
                    self.v_to_chain_pred[p.term]
                    for p in invars
                    if isinstance(p, ChainPredicate)
                }
            )
            self.abstract_effect_constant[gu] = constants
            self.abstract_effect[gu] = new_effects
            self.abstract_effect_ltl[gu] = gu_ltl
            self.t_u_to_curr_u[gu] = new_u_to_curr_u
            self.t_us_part[gu] = new_us_part
            self.t_us_part_to_pred[gu] = new_us_part_to_pred

        end = time.time()
        logger.info(end - start)

    def to_automaton_abstraction(self):
        raise NotImplementedError(
            "EffectsAbstraction: to_automaton_abstraction not implemented"
        )

    def get_symbol_table(self):
        return self.symbol_table

    def get_state_predicates(self):
        return self.state_predicates

    def get_raw_state_predicates(self):
        return self.raw_state_predicates

    def get_transition_predicates(self):
        return self.transition_predicates

    def get_raw_transition_predicates(self):
        return self.raw_transition_predicates

    def get_all_raw_preds(self):
        return self.get_raw_state_predicates() | self.get_raw_transition_predicates()

    def get_all_preds(self):
        return self.get_state_predicates() | self.get_transition_predicates()

    def get_ranking_and_invars(self):
        pass

    def get_program(self):
        return self.program

    def concretise_counterexample(self, counterexample: [dict]):
        pass


def update_constants_invars_chain_pre(p: ChainPredicate, gu, symbol_table, constants):
    if gu in p.last_pre.keys():
        last_pre = p.last_pre[gu]
        new_pre, _ = p.refine_old_pre_cond(last_pre, gu, symbol_table)
        if new_pre is None:
            constants.remove(last_pre)
            p.last_pre.pop(gu)
            return False, None
        else:
            if last_pre != new_pre:
                if last_pre not in constants:
                    print()
                else:
                    constants.remove(last_pre)
                constants.add(new_pre)
            return True, new_pre

    return False, None


def update_constants_invars_chain_post(p: ChainPredicate, gu, symbol_table, constants):
    if gu in p.last_post.keys():
        last_post = p.last_post[gu]
        new_post, _ = p.refine_old_post_cond(last_post, gu, symbol_table)
        if new_post is None:
            constants.remove(last_post)
            p.last_post.pop(gu)
            return False, None
        else:
            if last_post != new_post:
                if last_post not in constants:
                    print()
                else:
                    constants.remove(last_post)
                constants.add(new_post)
            return True, new_post

    return False, None


def update_invars(p: Predicate, gu, symbol_table, invars, constants):
    if isinstance(p, ChainPredicate):
        if p in invars:
            invars.remove(p)
            invars.add(p)
            return True
        else:
            x = p.is_invar(gu, symbol_table)
            if x is not None:
                invars.add(x)
                return True
    else:
        x = p.is_invar(gu, symbol_table)
        if x is not None:
            invars.add(x)
            return True
    return False


def update_pre(p: Predicate, gu, symbol_table, constants):
    if isinstance(p, ChainPredicate):
        result, pre = update_constants_invars_chain_pre(p, gu, symbol_table, constants)
        if result:
            return True, pre
        else:
            x = p.is_pre_cond(gu, symbol_table)
            if x is not None:
                constants.add(x)
                return True, x
    else:
        x = p.is_pre_cond(gu, symbol_table)
        if x is not None:
            constants.add(x)
            return True, x

    return False, None


def update_post(p: Predicate, gu, symbol_table, constants):
    if isinstance(p, ChainPredicate):
        result, post = update_constants_invars_chain_post(
            p, gu, symbol_table, constants
        )
        if result:
            return True, post
        else:
            x = p.is_post_cond(gu, symbol_table)
            if x is not None:
                new_post = x
                constants.add(new_post)
                return True, new_post
    else:
        x = p.is_post_cond(gu, symbol_table)
        if x is not None:
            new_post = x
            constants.add(new_post)
            return True, new_post
    return False, None


def fully_determined_guard(guard, effects, constants, symbol_table):
    pres = conjunct_formula_set(
        p
        for p in constants
        if isinstance(p, Variable)
        or (isinstance(p, UniOp) and isinstance(p.right, Variable))
    )
    return is_tautology(
        iff(
            guard,
            conjunct(
                pres,
                disjunct_formula_set(now_nexts[0] for now_nexts in effects),
            ),
        ),
        symbol_table,
    )


def join_parts(effects, parts_to_join, us_part_to_pred):
    if len(parts_to_join) == 0:
        raise Exception("join_parts called on empty parts_to_join")
    emptyNowNexts = [(true(), [true()])]

    parts_to_join_red = [
        (effects[old_part], us_part_to_pred[old_part])
        for old_part in parts_to_join
        if effects[old_part] != emptyNowNexts
    ]

    match len(parts_to_join_red):
        case 0:
            return emptyNowNexts, (set(), set())
        case 1:
            return parts_to_join_red[0]

    part = parts_to_join_red[0]
    new_part_effects = part[0]
    (new_now_preds, new_next_preds) = part[1]

    parts_remaining = parts_to_join_red[1:]

    for nowNexts, (now_preds, next_preds) in parts_remaining:
        if nowNexts == emptyNowNexts:
            continue
        old_part_effects = new_part_effects
        new_part_effects = []
        for new_now, new_nexts in old_part_effects:
            for now, nexts in nowNexts:
                new_part_effects.append(
                    (conjunct(new_now, now), list(set(nexts + new_nexts)))
                )
        new_part_effects = new_part_effects
        new_now_preds.update(now_preds)
        new_next_preds.update(next_preds)

    return new_part_effects, (new_now_preds, new_next_preds)


def update_effects(
    effects,
    us,
    gu,
    curr_preds,
    new_preds,
    partitions,
    v_to_partition,
    v_to_preds,
    ignore_in_nows,
    ignore_in_nexts,
    symbol_table,
):
    now_preds, next_preds = curr_preds
    now_vs_init = set(
        itertools.chain.from_iterable(
            u.right.variablesin() for u in us if u.left != u.right
        )
    )
    now_vs = set(
        itertools.chain.from_iterable(
            partitions[v_to_partition[v]] for v in now_vs_init
        )
    )
    new_now_preds = {
        p
        for v in now_vs
        for p in v_to_preds[v]
        if (p not in now_preds or p in new_preds) and p not in ignore_in_nows
    }

    now_preds.update(new_now_preds)

    next_vs_init = {u.left for u in us if u.left != u.right}
    next_vs = set(
        itertools.chain.from_iterable(
            partitions[v_to_partition[v]] for v in next_vs_init
        )
    )
    new_next_preds = {
        p
        for v in next_vs
        for p in v_to_preds[v]
        if (p not in next_preds or p in new_preds) and p not in ignore_in_nexts
    }
    next_preds.update(new_next_preds)

    # adding preds to now that are relevant to determining transition preds
    tran_pred_rel_vars = set()
    for p in next_preds | curr_preds[1]:
        # if isinstance(p, TransitionPredicate):
        tran_pred_rel_vars.update(p.vars)
        #     new_now_preds.update({p for v in p.vars for p in v_to_preds[v]
        #                           if (p not in now_preds or p in new_preds) and p not in ignore_in_nows and "_prev" not in str(p)})
        # now_preds.update(new_now_preds)

    more_nows_vs = set(
        itertools.chain.from_iterable(
            partitions[v_to_partition[v]] for v in tran_pred_rel_vars
        )
    )
    more_now_preds = {
        p
        for v in more_nows_vs
        for p in v_to_preds[v]
        if (p not in now_preds or p in new_preds) and p not in ignore_in_nows
    }
    new_now_preds.update(more_now_preds)
    now_preds.update(more_now_preds)

    common_preds = new_now_preds.intersection(new_next_preds)
    new_now_preds.difference_update(common_preds)
    new_next_preds.difference_update(common_preds)

    new_now_preds = sorted(list(new_now_preds), key=lambda p: str(p))
    for p in new_now_preds:
        effects = p.extend_effect_now(gu, effects, symbol_table)

    new_next_preds = sorted(list(new_next_preds), key=lambda p: str(p))
    for p in new_next_preds:
        effects = p.extend_effect_next(gu, effects, symbol_table)

    common_preds = sorted(list(common_preds), key=lambda p: str(p))
    for p in common_preds:
        # this is adding tran preds, don t need them if only safety
        if isinstance(p, TransitionPredicate):
            effects = p.extend_effect_next(gu, effects, symbol_table)
        else:
            effects = p.extend_effect(gu, effects, symbol_table)

    return effects


def compute_abstract_effect_for_guard_update(arg):
    (
        gu,
        invars,
        constants,
        conf,
        dual_env_props,
        effects,
        all_preds,
        new_preds,
        partitions,
        v_to_preds,
        v_to_partition,
        old_u_to_curr_u,
        old_us_part,
        old_us_part_to_pred,
        ignore_in_nows,
        ignore_in_nexts,
        vars_relabelling,
        symbol_table,
    ) = arg

    init_nows = []
    init_nexts = []
    pres = {}
    posts = {}

    # for new preds, compute at transition level if:
    # - it is a precondition
    # - it is a postcondition
    #
    # when updating effects, ignore preds that are preconditions and postconditions
    # chainpreds may stop having elements that are pre/postconditions once they get refined (which means they will be in new_preds,
    # at that point need to remove them from to ignore list.
    #
    # predicates that are not ever handled in nexts are invars (unless they are prev preds)

    for p in new_preds:
        if isinstance(p, TransitionPredicate):
            ignore_in_nows.add(p)
            is_post, x = update_post(p, gu, symbol_table, constants)
            if is_post:
                posts[p] = x
                ignore_in_nexts.add(p)
        else:
            is_pre, x = update_pre(p, gu, symbol_table, constants)
            if is_pre:
                pres[p] = x
                ignore_in_nows.add(p)
            else:
                if p in ignore_in_nows:
                    ignore_in_nows.remove(p)
            is_post, x = update_post(p, gu, symbol_table, constants)
            if is_post:
                posts[p] = x
                ignore_in_nexts.add(p)
                if is_pre:
                    continue
            else:
                if p in ignore_in_nexts:
                    ignore_in_nexts.remove(p)
            is_invar = update_invars(p, gu, symbol_table, invars, constants)
            if is_invar:
                ignore_in_nexts.add(p)
            else:
                if p in ignore_in_nexts and not is_post:
                    ignore_in_nexts.remove(p)

    curr_us_to_ignore = set()
    new_us_part = []
    new_u_to_curr_u = {}
    new_part_to_curr_parts = {}
    for curr_u in old_us_part:
        if curr_u in curr_us_to_ignore:
            continue
        curr_us_to_join = {curr_u}
        for u in curr_u:
            u_part = v_to_partition[u.left]
            part = partitions[u_part]
            right_parts = [v_to_partition[v] for v in u.right.variablesin()]
            for other_curr_u in old_us_part:
                if other_curr_u != curr_u:
                    if any(
                        True
                        for uu in other_curr_u
                        if uu.left in part
                        or any(
                            p
                            for p in right_parts
                            if p
                            in [v_to_partition[vv] for vv in uu.right.variablesin()]
                        )
                    ):
                        curr_us_to_join.add(other_curr_u)
                        # curr_us_to_join.update({old_u_to_curr_u[u] for u in part})

        new_part = frozenset(itertools.chain.from_iterable(curr_us_to_join))
        new_us_part.append(new_part)
        new_u_to_curr_u.update({u: new_part for u in curr_us_to_join})
        new_part_to_curr_parts[new_part] = curr_us_to_join
        curr_us_to_ignore.update(curr_us_to_join)

    # new_us_part tells which prev update parts to join together
    # old_us_part_to_pred tells us which preds are considered in effects (now and next) of old_us_part
    # effects will be of the form: old_us_part -> (now, [next])
    # TODO the below can be optimised
    no_changes = False
    new_new_part_to_curr_parts = {}
    while not no_changes:
        done_parts = set()
        no_changes = False
        for us_part1, old_part1 in new_part_to_curr_parts.items():
            if us_part1 in done_parts:
                continue
            no_changes = True
            new_us_part1 = set()
            old_us_part1 = set()
            new_us_part1.update(us_part1)
            old_us_part1.update(old_part1)
            done_parts.add(us_part1)
            for us_part2, old_part2 in new_part_to_curr_parts.items():
                if us_part2 not in done_parts:
                    if len(us_part1.intersection(us_part2)) != 0:
                        done_parts.add(us_part2)
                        new_us_part1.update(us_part2)
                        old_us_part1.update(old_part2)
                        no_changes = False

            new_new_part_to_curr_parts[frozenset(new_us_part1)] = old_us_part1

        new_part_to_curr_parts = new_new_part_to_curr_parts

    all_relevant_next_preds = set()
    new_effects = {}
    new_us_part_to_pred = {}
    for us_part, old_parts in new_part_to_curr_parts.items():
        us_part_effects_joined, curr_preds = join_parts(
            effects, list(old_parts), old_us_part_to_pred
        )
        us_part_effects = update_effects(
            us_part_effects_joined,
            us_part,
            gu,
            curr_preds,
            new_preds,
            partitions,
            v_to_partition,
            v_to_preds,
            ignore_in_nows,
            ignore_in_nexts,
            symbol_table,
        )
        new_effects[us_part] = us_part_effects
        new_us_part_to_pred[us_part] = curr_preds
        all_relevant_next_preds.update(curr_preds[1])
        init_nows.extend(curr_preds[0])
        init_nexts.extend(curr_preds[1])

    unused_new_preds = all_preds.difference(all_relevant_next_preds)
    unused_new_preds.difference_update(ignore_in_nexts)
    for p in unused_new_preds:
        if p.is_input:
            continue
        if isinstance(p, ChainPredicate):
            if p in invars:
                # an old version/copy of p may be in invars
                invars.remove(p)
            invars.add(p)
        else:
            invars.add(p.bool_var)

    gu_ltl = effects_to_ltl(
        gu, new_effects, constants, invars, conf, dual_env_props, vars_relabelling
    )

    if conf.debug:
        print("\n\n\n" + str(gu) + "\n" + str(gu_ltl))
        print("\n\n" + str(gu))

    return (
        gu,
        invars,
        constants,
        new_effects,
        new_u_to_curr_u,
        new_us_part,
        new_us_part_to_pred,
        (init_nows, init_nexts, pres, posts),
        ignore_in_nows,
        ignore_in_nexts,
        str(gu_ltl),
    )


def debug_check_sat(gu, now_nexts, invars, constants, symbol_table):
    for now, nexts in now_nexts:
        for next in nexts:
            f = conjunct_formula_set([gu, now.prev_rep(), next])
            if not sat(f, symbol_table):
                print("following not sat with transition: " + str(gu))
                print("now" + str(now))
                print("next" + str(next))


def effects_to_ltl(
    gu,
    effects,
    constants,
    invars,
    conf: config.Config,
    dual_env_props,
    vars_relabelling,
):
    parts_ltl = []
    for part in effects.keys():
        part_ltl = []
        for now, nexts in effects[part]:
            if len(nexts) == 1 and nexts[0] == true():
                continue
            E_now = now.replace_formulas(vars_relabelling)
            if conf.dual:
                E_now = X(massage_ltl_for_dual(E_now, dual_env_props))
                if conf.backend == "strix":
                    E_now = propagate_nexts(E_now)
            next_disjuncts = []
            if not (len(nexts) == 1 and nexts[0] == true()):
                for next in nexts:
                    next_f = X(next.replace_formulas(vars_relabelling))
                    if conf.dual:
                        next_f = X(next_f)
                    if conf.backend == "strix":
                        next_f = propagate_nexts(next_f)
                    next_disjuncts.append(next_f)

            E_next = disjunct_formula_set(next_disjuncts)
            part_ltl.append(conjunct(E_now, E_next))
        if len(part_ltl) != 0:
            parts_ltl.append(disjunct_formula_set(part_ltl))

    parts_ltl = sorted(parts_ltl, key=lambda f: str(f))
    effects_ltl = conjunct_formula_set(parts_ltl)

    invar_preds_effects = set()
    invars = sorted(set(invars), key=lambda p: str(p))
    for p in invars:
        if isinstance(p, ChainPredicate):
            if conf.dual:
                invar_preds_effects.update(iff(X(b), X(X(b))) for b in p.bin_vars)
            else:
                invar_preds_effects.update(iff(b, X(b)) for b in p.bin_vars)
        else:
            if "prev" not in str(p):
                if conf.dual:
                    invar_preds_effects.add(iff(X(p), X(X(p))))
                else:
                    invar_preds_effects.add(iff(p, X(p)))

    constant_effects = []
    constants = sorted(set(constants), key=lambda p: str(p))
    for p in constants:
        const = p.replace_formulas(vars_relabelling)
        if conf.dual:
            const = X(const)
        if conf.backend == "strix":
            constant_effects.append(propagate_nexts(const))
        else:
            constant_effects.append(const)

    gu_ltl = conjunct_formula_set(
        [effects_ltl] + list(invar_preds_effects) + constant_effects
    )

    return gu_ltl


def effects_to_ltl_non_bin(effects, constants, invars):
    parts_ltl = []
    for part in effects.keys():
        part_ltl = []
        for now, nexts in effects[part]:
            if len(nexts) == 1 and nexts[0] == true():
                continue

            E_now = now
            next_disjuncts = []
            for next in nexts:
                next_disjuncts.append(next)

            E_next = disjunct_formula_set(next_disjuncts)
            part_ltl.append(conjunct(E_now, (X(E_next))))
        if len(part_ltl) != 0:
            parts_ltl.append(disjunct_formula_set(part_ltl))

    effects_ltl = conjunct_formula_set(parts_ltl)

    invar_preds_effects = set()
    for p in set(invars):
        if isinstance(p, ChainPredicate):
            invar_preds_effects.update(iff(b, X(b)) for b in p.bin_vars)
        else:
            if "prev" not in str(p):
                invar_preds_effects.add(iff(p, X(p)))

    constant_effects = []
    for p in set(constants):
        constant_effects.append((p))

    gu_ltl = conjunct_formula_set(
        [effects_ltl] + list(invar_preds_effects) + constant_effects
    )
    print(gu_ltl)
