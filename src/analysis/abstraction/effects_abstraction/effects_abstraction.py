import itertools
import logging
import time
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.abs_util import (
    update_var_partition_mult,
)
from analysis.abstraction.effects_abstraction.predicates import StatePredicate
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import (
    ChainPredicate,
)
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.abstraction.effects_abstraction.predicates.Predicate import (
    Predicate,
)
from analysis.abstraction.effects_abstraction.predicates.TransitionPredicate import (
    TransitionPredicate,
)
from analysis.abstraction.interface.ltl_abstraction_type import (
    LTLAbstractionTransitionType,
    LTLAbstractionBaseType,
    LTLAbstractionStructureType,
    LTLAbstractionType,
    LTLAbstractionOutputType,
)
from analysis.abstraction.interface.predicate_abstraction import (
    PredicateAbstraction,
)
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import (
    AbstractLTLSynthesisProblem,
)
from synthesis.ltl_synthesis import parse_hoa
from synthesis.mealy_machine import MealyMachine
from programs.typed_valuation import TypedValuation
from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.util import (
    conjunct,
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
)

logger = logging.getLogger(__name__)


class EffectsAbstraction(PredicateAbstraction):
    def get_interpolants(self) -> [Formula]:
        pass

    def __init__(self, program: Program, old_to_new_st_preds):
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}
        self.abstract_effect_ltl = {}
        self.abstract_effect_tran_preds_constant = {}

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

        self.init_conf = None
        self.init_state_abstraction = []
        self.second_state_abstraction = {}

        self.init_program_trans = None
        self.non_init_program_trans = None

        self.init_program_gus = None
        self.non_init_program_gus = None
        self.gu_to_trans = {}

        self.wrapped_preds = set()
        self.state_predicates = set()
        self.chain_state_predicates = set()
        self.transition_predicates = set()
        self.chain_rep = {}

        self.current_chain_all_bin_rep = {}
        self.pred_to_v = {}

        self.ranking_constraints = {}
        self.structural_loop_constraints = []
        self.loops = []
        self.var_relabellings = {}

        self.program = program
        self.loop_counter = 0

        logger.info("Initialising predicate abstraction.")

        self.abstract_program_transitions(old_to_new_st_preds)

        self.symbol_table = {v: tv for v, tv in program.symbol_table.items()}

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
        self.init_conf = conjunct_typed_valuation_set(self.program.valuation)
        self.init_program_trans = {
            t
            for t in all_trans
            if t.src == self.program.initial_state
            and sat(
                conjunct(self.init_conf.prev_rep(), t.formula()),
                self.program.symbol_table,
            )
        }
        for t in self.init_program_trans:
            gu = t.formula()
            if gu in self.gu_to_trans.keys():
                self.gu_to_trans[gu].append(t)
            else:
                self.gu_to_trans[gu] = [t]

        self.init_program_gus = {t.formula() for t in self.init_program_trans}

        self.non_init_program_trans = all_trans
        self.non_init_program_gus = {t.formula() for t in self.non_init_program_trans}

        for t in self.non_init_program_trans:
            gu = t.formula()
            if gu in self.gu_to_trans.keys():
                self.gu_to_trans[gu].append(t)
            else:
                self.gu_to_trans[gu] = [t]

        for gu in self.init_program_gus:
            self.second_state_abstraction[gu] = []

        for gu in self.non_init_program_gus:
            self.abstract_effect_ltl[gu] = true()
            self.abstract_effect_invars[gu] = set()
            self.abstract_effect_constant[gu] = set()
            self.abstract_effect_tran_preds_constant[gu] = []

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
        parallelise=True,
    ):

        self.add_state_predicates(
            new_state_predicates | new_transition_predicates, parallelise
        )

    def add_ranking_constraints(
        self, new_ranking_constraints: dict[Formula, [Formula]]
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

    def add_structural_loop_constraints(self, new_structural_loop_constraints):
        for constraint in new_structural_loop_constraints:
            processed_ltl_constraints = []
            processed = strip_mathexpr(constraint)
            processed_ltl_constraints.append(processed)
            self.structural_loop_constraints.extend(processed_ltl_constraints)

    def add_state_predicates(self, new_state_predicates: [Formula], parallelise=True):
        if len(new_state_predicates) == 0:
            return
        # assuming input state predicates have been normalised (all of type < or <=, and vars on LHS and constants on RHS)

        logger.info("Adding predicates to predicate abstraction:")
        logger.info(
            "state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]"
        )

        logger.info("Tagging abstract transitions with predicates..")
        start = time.time()

        use_chain_preds = not config.Config.getConfig().no_binary_enc
        remaining_st_preds = list(new_state_predicates)

        new_preds = set()

        accelerate = config.Config.getConfig().eager_fairness

        if use_chain_preds:
            term_to_p_for_chain = {}
            remaining_st_preds = []
            for p in new_state_predicates:
                if isinstance(p, BiOp) and p.op[0] == "<":
                    if p.left not in term_to_p_for_chain.keys():
                        term_to_p_for_chain[p.left] = [p]
                    else:
                        term_to_p_for_chain[p.left].append(p)
                else:
                    f_p = StatePredicate(p)
                    remaining_st_preds.append(f_p)
                    new_preds.add(f_p)
                    self.state_predicates.add(f_p)
                    self.var_relabellings.update(f_p.boolean_rep())

            for term, preds in term_to_p_for_chain.items():
                self.chain_state_predicates.update(preds)
                new_chain_pred = False
                if term not in self.v_to_chain_pred.keys():
                    v_chain_pred = ChainPredicate(term, self.program, accelerate)
                    self.v_to_chain_pred[term] = v_chain_pred
                    new_chain_pred = True
                else:
                    v_chain_pred = self.v_to_chain_pred[term]

                v_chain_pred.add_predicate(preds)

                if new_chain_pred and accelerate and len(v_chain_pred.tran_preds) > 0:
                    gu = TransitionPredicate(v_chain_pred.tran_preds)
                    new_preds.add(gu)
                    self.transition_predicates.add(gu)
                    self.var_relabellings.update(gu.boolean_rep())
                    remaining_st_preds.append(gu)
                new_preds.add(v_chain_pred)

                self.var_relabellings.update(v_chain_pred.boolean_rep())

                if new_chain_pred:
                    for p in v_chain_pred.chain:
                        # TODO if transition pred need to set neg of every pred
                        if sat(conjunct(self.init_conf, p), self.symbol_table):
                            self.init_state_abstraction.append(p)
                            break

                    for gu in self.init_program_gus:
                        for p in v_chain_pred.chain:
                            if sat(
                                conjunct(conjunct(self.init_conf.prev_rep(), gu), p),
                                self.symbol_table,
                            ):
                                self.second_state_abstraction[gu].append(p)
                                break
                else:
                    old_to_new = v_chain_pred.old_to_new
                    for old_p in old_to_new.keys():
                        # TODO if transition pred do not update
                        if old_p in self.init_state_abstraction:
                            self.init_state_abstraction.remove(old_p)
                            for p in old_to_new[old_p]:
                                if sat(
                                    conjunct(self.init_conf, p),
                                    self.symbol_table,
                                ):
                                    self.init_state_abstraction.append(p)
                                    break

                    for gu in self.init_program_gus:
                        for old_p in old_to_new.keys():
                            if old_p in self.second_state_abstraction[gu]:
                                self.second_state_abstraction[gu].remove(old_p)
                                for p in old_to_new[old_p]:
                                    if sat(
                                        conjunct(
                                            conjunct(self.init_conf.prev_rep(), gu),
                                            p,
                                        ),
                                        self.symbol_table,
                                    ):
                                        self.second_state_abstraction[gu].append(p)
                                        break
        else:
            for p in remaining_st_preds:
                f_p = StatePredicate(p)
                new_preds.add(f_p)
                self.state_predicates.add(f_p)
                self.var_relabellings.update(f_p.boolean_rep())
            remaining_st_preds = new_preds

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
                    {
                        str(bool_var): TypedValuation(str(bool_var), "bool", true())
                        for bool_var in p.bool_rep.values()
                    }
                )

                self.init_state_abstraction.append(p.stutter)
                for gu in self.init_program_gus:
                    for option in p.options:
                        if sat(
                            conjunct(conjunct(self.init_conf.prev_rep(), gu), option),
                            self.symbol_table,
                        ):
                            self.second_state_abstraction[gu].append(option)
                            break
            else:
                self.symbol_table.update(
                    {str(p.bool_var): TypedValuation(str(p.bool_var), "bool", true())}
                )
                if "_prev" in str(p):
                    if sat(
                        conjunct(
                            conjunct(self.init_conf.prev_rep(), self.init_conf),
                            p.pred,
                        ),
                        self.symbol_table,
                    ):
                        self.init_state_abstraction.append(p.pred)
                    else:
                        self.init_state_abstraction.append(neg(p.pred))
                else:
                    if sat(conjunct(self.init_conf, p.pred), self.symbol_table):
                        self.init_state_abstraction.append(p.pred)
                    else:
                        self.init_state_abstraction.append(neg(p.pred))

                for gu in self.init_program_gus:
                    if sat(
                        conjunct(conjunct(self.init_conf.prev_rep(), gu), p.pred),
                        self.symbol_table,
                    ):
                        self.second_state_abstraction[gu].append(p.pred)
                    else:
                        self.second_state_abstraction[gu].append(neg(p.pred))

        no_of_workers = config.Config.getConfig().workers if parallelise else 1

        all_preds = self.state_predicates | set(self.v_to_chain_pred.values())

        new_preds = list(new_preds)
        # we do this sorting to ensure deterministic behaviour in abstraction, in case of bugs
        new_preds.sort(key=lambda x: str(x))

        gus = []
        gu_invars = []
        gu_constants = []
        gu_tran_preds_constants = []
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
        for gu in self.non_init_program_gus:
            gus.append(gu)
            gu_invars.append(self.abstract_effect_invars[gu])
            gu_constants.append(self.abstract_effect_constant[gu])
            gu_tran_preds_constants.append(self.abstract_effect_tran_preds_constant[gu])
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
                    gu_tran_preds_constants,
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

    def get_transition_predicates(self):
        return self.transition_predicates

    def get_ranking_and_invars(self):
        pass

    def get_program(self):
        return self.program

    def massage_mealy_machine(
        self,
        mm_hoa: str,
        base_abstraction,
        ltlAbstractionType: LTLAbstractionType,
        synthesis_problem: AbstractLTLSynthesisProblem,
        controller: bool,
    ) -> MealyMachine:
        if (
            ltlAbstractionType.base_type == LTLAbstractionBaseType.explicit_automaton
            and ltlAbstractionType.transition_type
            == LTLAbstractionTransitionType.combined
            and ltlAbstractionType.structure_type
            == LTLAbstractionStructureType.control_and_predicate_state
            and ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env
        ):

            mm = parse_hoa(
                synthesis_problem,
                output=mm_hoa,
                env_con_separate=False,
                abstraction=self,
            )

            if controller:
                return mm
            else:
                return mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(
                    self, self.program, base_abstraction
                )
        elif (
            ltlAbstractionType.base_type
            == LTLAbstractionBaseType.effects_representation
            and ltlAbstractionType.transition_type
            == LTLAbstractionTransitionType.env_con_separate
            and ltlAbstractionType.structure_type
            == LTLAbstractionStructureType.control_state
            and ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env
        ):

            mm = parse_hoa(
                synthesis_problem,
                output=mm_hoa,
                env_con_separate=True,
                abstraction=self,
            )

            return mm
        elif (
            ltlAbstractionType.base_type
            == LTLAbstractionBaseType.effects_representation
            and ltlAbstractionType.transition_type
            == LTLAbstractionTransitionType.one_trans
            and ltlAbstractionType.structure_type
            == LTLAbstractionStructureType.control_state
            and ltlAbstractionType.output_type == LTLAbstractionOutputType.no_output
        ):

            mm = parse_hoa(
                synthesis_problem,
                output=mm_hoa,
                env_con_separate=False,
                abstraction=self,
                one_trans=True,
            )

            return mm

        else:
            raise NotImplementedError(
                "Options for LTL abstraction not implemented: "
                + str(ltlAbstractionType)
            )

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

    for p in new_now_preds:
        effects = p.extend_effect_now(gu, effects, symbol_table)

    for p in new_next_preds:
        effects = p.extend_effect_next(gu, effects, symbol_table)

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
        tran_preds_constants,
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
            for other_curr_u in old_us_part:
                if other_curr_u != curr_u:
                    if any(
                        True
                        for uu in other_curr_u
                        if uu.left in part
                        or any(
                            True
                            for v in uu.right.variablesin()
                            if v in u.right.variablesin()
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
        if isinstance(p, ChainPredicate):
            if p in invars:
                # an old version/copy of p may be in invars
                invars.remove(p)
            invars.add(p)
        else:
            invars.add(p.bool_var)

    gu_ltl = effects_to_ltl(new_effects, constants, invars, vars_relabelling)
    print("\n\n\n" + str(gu) + "\n" + str(gu_ltl))

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


def effects_to_ltl(effects, constants, invars, vars_relabelling):
    parts_ltl = []
    for part in effects.keys():
        part_ltl = []
        for now, nexts in effects[part]:
            if len(nexts) == 1 and nexts[0] == true():
                continue

            E_now = now.replace_formulas(vars_relabelling)
            next_disjuncts = []
            for next in nexts:
                next_disjuncts.append(next.replace_formulas(vars_relabelling))

            E_next = disjunct_formula_set(next_disjuncts)
            part_ltl.append(conjunct(E_now, propagate_nexts(X(E_next))))
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
        constant_effects.append(propagate_nexts(p.replace_formulas(vars_relabelling)))

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
