from unittest import TestCase

from parsing.string_to_program_with_action_guards import string_to_program
from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from analysis.abstraction.concretisation import concretize_transitions
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from analysis.refinement.fairness_refinement.ranking_refinement import try_liveness_refinement
from analysis.refinement.safety_refinement.interpolation_refinement import safety_refinement
from programs.util import parse_nuxmv_ce_output_finite


class Test(TestCase):
    def test_safety_refinement(self):
        with open('../examples/parallel/road/program.prog') as program_file:
            program = string_to_program(program_file.read())
            predicate_abstraction = EffectsAbstraction(program)
            state_predicates = list(map(string_to_prop, ["cr <= 0", "cr <= 0"]))
            invar = string_to_prop("(-3*cr + 1) <= 0")
            ranking = string_to_math_expression("(-3*cr + 1)")
            # ranking_invars = {ranking: [invar]}
            ranking_invars = {}
            predicate_abstraction.add_predicates(state_predicates, {})
            predicate_abstraction.add_predicates([], ranking_invars)

            ce, transition_indices_and_state, incompatible_state = parse_nuxmv_ce_output_finite(
                len(program.env_transitions) + len(program.con_transitions), counterexample2)
            transitions_without_stutter_program_took, env_desired_abstract_state, _ = \
                concretize_transitions(program,
                                       program,
                                       predicate_abstraction,
                                       transition_indices_and_state,
                                       incompatible_state)

            # if pred_state is not None:
            agreed_on_transitions = transitions_without_stutter_program_took
            # removing transition predicates for now
            disagreed_on_state = ([string_to_prop("(!((!(0 < cl) | !(0 <= cl)) & ((cr - 1) = 0) & (cl = 0) & (0 < cr) & (0 <= cr)) & (0 <= cl) & (0 <= cr))")], env_desired_abstract_state[1])
            # disagreed_on_state = ([p for p in env_desired_abstract_state[0]], env_desired_abstract_state[1])

            counterstrategy_states = [key for ce_state in ce for key, v in ce_state.items()
                                      if key.startswith("st_")
                                      and (ce_state["turn"] in ["env", "con"])
                                      and "_seen" not in key
                                      and v == "TRUE"]

            write_counterexample_print(program, agreed_on_transitions, disagreed_on_state)

            success, result = try_liveness_refinement(counterstrategy_states,
                                                      program,
                                                      predicate_abstraction,
                                                      agreed_on_transitions,
                                                      disagreed_on_state,
                                                      ranking_invars,
                                                      False)

            success, result = safety_refinement(program,
                                                predicate_abstraction,
                                                agreed_on_transitions,
                                                disagreed_on_state,
                                                ce,
                                                False,
                                                False,
                                                False)
            self.assertTrue(len(result) == 2)
            self.assertTrue(string_to_prop("cr = 1") in result)
            self.assertTrue(string_to_prop("cl = 0") in result)


counterexample2 = """INFO     *** This is nuXmv 2.0.0 (compiled on Mon Oct 14 18:05:39 2019)
*** Copyright (c) 2014-2019, Fondazione Bruno Kessler
*** For more information on nuXmv see https://nuxmv.fbk.eu
*** or email to <nuxmv@list.fbk.eu>.
*** Please report bugs at https://nuxmv.fbk.eu/bugs
*** (click on "Login Anonymously" to access)
*** Alternatively write to <nuxmv@list.fbk.eu>.

*** This version of nuXmv is linked to NuSMV 2.6.0.
*** For more information on NuSMV see <http://nusmv.fbk.eu>
*** or email to <nusmv-users@list.fbk.eu>.
*** Copyright (C) 2010-2019, Fondazione Bruno Kessler

*** This version of nuXmv is linked to the CUDD library version 2.4.1
*** Copyright (c) 1995-2004, Regents of the University of Colorado

*** This version of nuXmv is linked to the MiniSat SAT solver. 
*** See http://minisat.se/MiniSat.html
*** Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
*** Copyright (c) 2007-2010, Niklas Sorensson

*** This version of nuXmv is linked to MathSAT
*** Copyright (C) 2009-2019 by Fondazione Bruno Kessler
*** Copyright (C) 2009-2019 by University of Trento and others
*** See http://mathsat.fbk.eu

-- no proof or counterexample found with bound 0
-- no proof or counterexample found with bound 1
-- no proof or counterexample found with bound 2
-- no proof or counterexample found with bound 3
-- no proof or counterexample found with bound 4
-- no proof or counterexample found with bound 5
-- no proof or counterexample found with bound 6
-- no proof or counterexample found with bound 7
-- no proof or counterexample found with bound 8
-- no proof or counterexample found with bound 9
-- no proof or counterexample found with bound 10
-- LTL specification  G !mismatch  is false
-- as demonstrated by the following execution sequence
Trace Description: IC3 smt counterexample 
Trace Type: Counterexample 
  -> State: 1.1 <-
    cl = 0
    cl_prev = 0
    cr = 0
    cr_prev = -1
    danger = FALSE
    empty_l = FALSE
    empty_r = FALSE
    entry_l = FALSE
    entry_r = FALSE
    error = FALSE
    exit_l = FALSE
    exit_r = FALSE
    l2r = TRUE
    q0 = TRUE
    q1 = FALSE
    stop_l = FALSE
    stop_r = TRUE
    turn = env
    env_turn = FALSE
    mon_danger = FALSE
    mon_empty_l = TRUE
    mon_empty_r = TRUE
    mon_error = FALSE
    mon_q0 = TRUE
    mon_q1 = FALSE
    pred_____MINUS_3_MULT_cr__PLUS_1__GT__EQ_0_ = TRUE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__LT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    pred__cl_LT__EQ_0_ = TRUE
    pred__cr_LT__EQ_0_ = TRUE
    st_0 = FALSE
    st_0_0 = FALSE
    st_13_0 = FALSE
    st_14_0 = FALSE
    st_16_0 = FALSE
    st_17_0 = FALSE
    st_18_0 = FALSE
    st_19_0 = FALSE
    st_1_0 = FALSE
    st_2_0 = FALSE
    st_3_0 = FALSE
    st_4_0 = FALSE
    st__10_0 = TRUE
    st__11_0 = FALSE
    st__12_0 = FALSE
    st__15_0 = FALSE
    st__5_0 = FALSE
    st__6_0 = FALSE
    st__7_0 = FALSE
    st__8_0 = FALSE
    st__9_0 = FALSE
    st_0_seen_once = FALSE
    st_0_0_seen_once = FALSE
    st_13_0_seen_once = FALSE
    st_14_0_seen_once = FALSE
    st_16_0_seen_once = FALSE
    st_17_0_seen_once = FALSE
    st_18_0_seen_once = FALSE
    st_19_0_seen_once = FALSE
    st_1_0_seen_once = FALSE
    st_2_0_seen_once = FALSE
    st_3_0_seen_once = FALSE
    st_4_0_seen_once = FALSE
    st__10_0_seen_once = FALSE
    st__11_0_seen_once = FALSE
    st__12_0_seen_once = FALSE
    st__15_0_seen_once = FALSE
    st__5_0_seen_once = FALSE
    st__6_0_seen_once = FALSE
    st__7_0_seen_once = FALSE
    st__8_0_seen_once = FALSE
    st__9_0_seen_once = FALSE
    st_0_seen_more_than_once = FALSE
    st_0_0_seen_more_than_once = FALSE
    st_13_0_seen_more_than_once = FALSE
    st_14_0_seen_more_than_once = FALSE
    st_16_0_seen_more_than_once = FALSE
    st_17_0_seen_more_than_once = FALSE
    st_18_0_seen_more_than_once = FALSE
    st_19_0_seen_more_than_once = FALSE
    st_1_0_seen_more_than_once = FALSE
    st_2_0_seen_more_than_once = FALSE
    st_3_0_seen_more_than_once = FALSE
    st_4_0_seen_more_than_once = FALSE
    st__10_0_seen_more_than_once = FALSE
    st__11_0_seen_more_than_once = FALSE
    st__12_0_seen_more_than_once = FALSE
    st__15_0_seen_more_than_once = FALSE
    st__5_0_seen_more_than_once = FALSE
    st__6_0_seen_more_than_once = FALSE
    st__7_0_seen_more_than_once = FALSE
    st__8_0_seen_more_than_once = FALSE
    st__9_0_seen_more_than_once = FALSE
    mismatch = FALSE
    compatible_tran_predicates = TRUE
    compatible_state_predicates = TRUE
    compatible = TRUE
    compatible_states = TRUE
    compatible_outputs = TRUE
    counterstrategy_guard_19 = FALSE
    counterstrategy_guard_18 = FALSE
    counterstrategy_guard_17 = FALSE
    counterstrategy_guard_16 = FALSE
    counterstrategy_guard_15 = FALSE
    counterstrategy_guard_14 = FALSE
    counterstrategy_guard_13 = FALSE
    counterstrategy_guard_12 = FALSE
    counterstrategy_guard_11 = FALSE
    counterstrategy_guard_10 = FALSE
    counterstrategy_guard_9 = FALSE
    counterstrategy_guard_8 = FALSE
    counterstrategy_guard_7 = FALSE
    counterstrategy_guard_6 = FALSE
    counterstrategy_guard_5 = FALSE
    counterstrategy_guard_4 = FALSE
    counterstrategy_guard_3 = FALSE
    counterstrategy_guard_2 = FALSE
    counterstrategy_guard_1 = FALSE
    counterstrategy_guard_0 = FALSE
    guard_27 = FALSE
    guard_26 = FALSE
    guard_25 = FALSE
    guard_24 = TRUE
    guard_23 = FALSE
    guard_22 = FALSE
    guard_21 = FALSE
    guard_20 = FALSE
    guard_19 = FALSE
    guard_18 = FALSE
    guard_17 = FALSE
    guard_16 = FALSE
    guard_15 = FALSE
    guard_14 = FALSE
    guard_13 = FALSE
    guard_12 = FALSE
    guard_11 = FALSE
    guard_10 = FALSE
    guard_9 = FALSE
    guard_8 = FALSE
    guard_7 = FALSE
    guard_6 = FALSE
    guard_5 = FALSE
    guard_4 = FALSE
    guard_3 = FALSE
    guard_2 = FALSE
    guard_1 = FALSE
    guard_0 = FALSE
    counterstrategy_act_19 = FALSE
    counterstrategy_act_18 = FALSE
    counterstrategy_act_17 = FALSE
    counterstrategy_act_16 = FALSE
    counterstrategy_act_15 = FALSE
    counterstrategy_act_14 = FALSE
    counterstrategy_act_13 = TRUE
    counterstrategy_act_12 = FALSE
    counterstrategy_act_11 = FALSE
    counterstrategy_act_10 = FALSE
    counterstrategy_act_9 = TRUE
    counterstrategy_act_8 = FALSE
    counterstrategy_act_7 = FALSE
    counterstrategy_act_6 = FALSE
    counterstrategy_act_5 = FALSE
    counterstrategy_act_4 = FALSE
    counterstrategy_act_3 = FALSE
    counterstrategy_act_2 = FALSE
    counterstrategy_act_1 = FALSE
    counterstrategy_act_0 = FALSE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_26 = FALSE
    act_25 = FALSE
    act_24 = TRUE
    act_23 = FALSE
    act_22 = FALSE
    act_21 = FALSE
    act_20 = FALSE
    act_19 = FALSE
    act_18 = FALSE
    act_17 = FALSE
    act_16 = FALSE
    act_15 = FALSE
    act_14 = FALSE
    act_13 = FALSE
    act_12 = FALSE
    act_11 = FALSE
    act_10 = FALSE
    act_9 = FALSE
    act_8 = FALSE
    act_7 = FALSE
    act_6 = FALSE
    act_5 = FALSE
    act_4 = FALSE
    act_3 = FALSE
    act_2 = FALSE
    act_1 = FALSE
    act_0 = FALSE
  -> State: 1.2 <-
    cr_prev = 0
    empty_l = TRUE
    empty_r = TRUE
    turn = mon_env
    counterstrategy_guard_5 = TRUE
    guard_27 = TRUE
    guard_24 = FALSE
    counterstrategy_act_13 = FALSE
    counterstrategy_act_9 = FALSE
    counterstrategy_act_5 = TRUE
    identity_counterstrategy = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_24 = FALSE
    act_8 = TRUE
  -> State: 1.3 <-
    empty_l = FALSE
    empty_r = FALSE
    exit_l = TRUE
    exit_r = TRUE
    stop_l = TRUE
    stop_r = FALSE
    turn = con
    mon_empty_l = FALSE
    mon_empty_r = FALSE
    st_2_0 = TRUE
    st__10_0 = FALSE
    counterstrategy_guard_5 = FALSE
    identity_counterstrategy = TRUE
  -> State: 1.4 <-
    turn = mon_con
    counterstrategy_guard_11 = TRUE
    counterstrategy_act_11 = TRUE
    counterstrategy_act_5 = FALSE
    identity_counterstrategy = FALSE
  -> State: 1.5 <-
    entry_r = TRUE
    exit_l = FALSE
    stop_l = FALSE
    turn = env
    mon_empty_l = TRUE
    pred_____MINUS_3_MULT_cr__PLUS_1__GT__EQ_0_ = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = TRUE
    pred__cr_LT__EQ_0_ = FALSE
    st_2_0 = FALSE
    st__5_0 = TRUE
    st_18_0_seen_once = TRUE
    counterstrategy_guard_11 = FALSE
    guard_27 = FALSE
    guard_17 = TRUE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_17 = TRUE
    act_8 = FALSE
  -> State: 1.6 <-
    cr = 1
    empty_l = TRUE
    turn = mon_env
    st_18_0_seen_once = FALSE
    counterstrategy_guard_0 = TRUE
    guard_27 = TRUE
    guard_17 = FALSE
    counterstrategy_act_11 = FALSE
    counterstrategy_act_2 = TRUE
    counterstrategy_act_0 = TRUE
    identity_counterstrategy = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_17 = FALSE
    act_8 = TRUE
  -> State: 1.7 <-
    empty_l = FALSE
    entry_l = TRUE
    l2r = FALSE
    stop_l = TRUE
    turn = con
    mon_empty_l = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    st_17_0 = TRUE
    st__5_0 = FALSE
    counterstrategy_guard_0 = FALSE
    identity_counterstrategy = TRUE
  -> State: 1.8 <-
    cr_prev = 1
    turn = mon_con
    counterstrategy_guard_17 = TRUE
    counterstrategy_act_17 = TRUE
    counterstrategy_act_2 = FALSE
    counterstrategy_act_0 = FALSE
    identity_counterstrategy = FALSE
  -> State: 1.9 <-
    entry_l = FALSE
    entry_r = FALSE
    exit_l = TRUE
    l2r = TRUE
    stop_l = FALSE
    stop_r = TRUE
    turn = env
    mon_empty_l = TRUE
    pred_____MINUS_3_MULT_crprev__PLUS_1__LT____MINUS_3_MULT_cr__PLUS_1__ = TRUE
    st_17_0 = FALSE
    st__7_0 = TRUE
    counterstrategy_guard_17 = FALSE
    guard_27 = FALSE
    guard_22 = TRUE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_22 = TRUE
    act_8 = FALSE
  -> State: 1.10 <-
    cr = 0
    empty_l = TRUE
    empty_r = TRUE
    turn = mon_env
    compatible_state_predicates = FALSE
    compatible = FALSE
    compatible_outputs = FALSE
    counterstrategy_guard_2 = TRUE
    guard_27 = TRUE
    guard_22 = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_22 = FALSE
    act_8 = TRUE
  -> State: 1.11 <-
    empty_l = FALSE
    empty_r = FALSE
    mismatch = TRUE
  -- Loop starts here
  -> State: 1.12 <-
    cr_prev = -1
    compatible_tran_predicates = FALSE
  -> State: 1.13 <-
  -> State: 1.14 <-"""

counterexample = """INFO     *** This is nuXmv 2.0.0 (compiled on Mon Oct 14 18:05:39 2019)
*** Copyright (c) 2014-2019, Fondazione Bruno Kessler
*** For more information on nuXmv see https://nuxmv.fbk.eu
*** or email to <nuxmv@list.fbk.eu>.
*** Please report bugs at https://nuxmv.fbk.eu/bugs
*** (click on "Login Anonymously" to access)
*** Alternatively write to <nuxmv@list.fbk.eu>.

*** This version of nuXmv is linked to NuSMV 2.6.0.
*** For more information on NuSMV see <http://nusmv.fbk.eu>
*** or email to <nusmv-users@list.fbk.eu>.
*** Copyright (C) 2010-2019, Fondazione Bruno Kessler

*** This version of nuXmv is linked to the CUDD library version 2.4.1
*** Copyright (c) 1995-2004, Regents of the University of Colorado

*** This version of nuXmv is linked to the MiniSat SAT solver. 
*** See http://minisat.se/MiniSat.html
*** Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
*** Copyright (c) 2007-2010, Niklas Sorensson

*** This version of nuXmv is linked to MathSAT
*** Copyright (C) 2009-2019 by Fondazione Bruno Kessler
*** Copyright (C) 2009-2019 by University of Trento and others
*** See http://mathsat.fbk.eu

-- no proof or counterexample found with bound 0
-- no proof or counterexample found with bound 1
-- no proof or counterexample found with bound 2
-- no proof or counterexample found with bound 3
-- no proof or counterexample found with bound 4
-- no proof or counterexample found with bound 5
-- no proof or counterexample found with bound 6
-- no proof or counterexample found with bound 7
-- no proof or counterexample found with bound 8
-- no proof or counterexample found with bound 9
-- no proof or counterexample found with bound 10
-- LTL specification  G !mismatch  is false
-- as demonstrated by the following execution sequence
Trace Description: IC3 smt counterexample 
Trace Type: Counterexample 
  -> State: 1.1 <-
    cl = 0
    cl_prev = 0
    cr = 0
    cr_prev = -1
    danger = FALSE
    empty_l = FALSE
    empty_r = FALSE
    entry_l = FALSE
    entry_r = FALSE
    error = FALSE
    exit_l = FALSE
    exit_r = FALSE
    l2r = TRUE
    q0 = TRUE
    q1 = FALSE
    stop_l = FALSE
    stop_r = TRUE
    turn = env
    env_turn = FALSE
    mon_danger = FALSE
    mon_empty_l = TRUE
    mon_empty_r = TRUE
    mon_error = FALSE
    mon_q0 = TRUE
    mon_q1 = FALSE
    pred_____MINUS_3_MULT_cr__PLUS_1__GT__EQ_0_ = TRUE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__LT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    pred__cl_LT__EQ_0_ = TRUE
    pred__cr_LT__EQ_0_ = TRUE
    st_0 = FALSE
    st_0_0 = FALSE
    st_13_0 = FALSE
    st_14_0 = FALSE
    st_16_0 = FALSE
    st_17_0 = FALSE
    st_18_0 = FALSE
    st_19_0 = FALSE
    st_1_0 = FALSE
    st_2_0 = FALSE
    st_3_0 = FALSE
    st_4_0 = FALSE
    st__10_0 = TRUE
    st__11_0 = FALSE
    st__12_0 = FALSE
    st__15_0 = FALSE
    st__5_0 = FALSE
    st__6_0 = FALSE
    st__7_0 = FALSE
    st__8_0 = FALSE
    st__9_0 = FALSE
    st_0_seen_once = FALSE
    st_0_0_seen_once = FALSE
    st_13_0_seen_once = FALSE
    st_14_0_seen_once = FALSE
    st_16_0_seen_once = FALSE
    st_17_0_seen_once = FALSE
    st_18_0_seen_once = FALSE
    st_19_0_seen_once = FALSE
    st_1_0_seen_once = FALSE
    st_2_0_seen_once = FALSE
    st_3_0_seen_once = FALSE
    st_4_0_seen_once = FALSE
    st__10_0_seen_once = FALSE
    st__11_0_seen_once = FALSE
    st__12_0_seen_once = FALSE
    st__15_0_seen_once = FALSE
    st__5_0_seen_once = FALSE
    st__6_0_seen_once = FALSE
    st__7_0_seen_once = FALSE
    st__8_0_seen_once = FALSE
    st__9_0_seen_once = FALSE
    st_0_seen_more_than_once = FALSE
    st_0_0_seen_more_than_once = FALSE
    st_13_0_seen_more_than_once = FALSE
    st_14_0_seen_more_than_once = FALSE
    st_16_0_seen_more_than_once = FALSE
    st_17_0_seen_more_than_once = FALSE
    st_18_0_seen_more_than_once = FALSE
    st_19_0_seen_more_than_once = FALSE
    st_1_0_seen_more_than_once = FALSE
    st_2_0_seen_more_than_once = FALSE
    st_3_0_seen_more_than_once = FALSE
    st_4_0_seen_more_than_once = FALSE
    st__10_0_seen_more_than_once = FALSE
    st__11_0_seen_more_than_once = FALSE
    st__12_0_seen_more_than_once = FALSE
    st__15_0_seen_more_than_once = FALSE
    st__5_0_seen_more_than_once = FALSE
    st__6_0_seen_more_than_once = FALSE
    st__7_0_seen_more_than_once = FALSE
    st__8_0_seen_more_than_once = FALSE
    st__9_0_seen_more_than_once = FALSE
    mismatch = FALSE
    compatible_tran_predicates = TRUE
    compatible_state_predicates = TRUE
    compatible = TRUE
    compatible_states = TRUE
    compatible_outputs = TRUE
    counterstrategy_guard_19 = FALSE
    counterstrategy_guard_18 = FALSE
    counterstrategy_guard_17 = FALSE
    counterstrategy_guard_16 = FALSE
    counterstrategy_guard_15 = FALSE
    counterstrategy_guard_14 = FALSE
    counterstrategy_guard_13 = FALSE
    counterstrategy_guard_12 = FALSE
    counterstrategy_guard_11 = FALSE
    counterstrategy_guard_10 = FALSE
    counterstrategy_guard_9 = FALSE
    counterstrategy_guard_8 = FALSE
    counterstrategy_guard_7 = FALSE
    counterstrategy_guard_6 = FALSE
    counterstrategy_guard_5 = FALSE
    counterstrategy_guard_4 = FALSE
    counterstrategy_guard_3 = FALSE
    counterstrategy_guard_2 = FALSE
    counterstrategy_guard_1 = FALSE
    counterstrategy_guard_0 = FALSE
    guard_27 = FALSE
    guard_26 = FALSE
    guard_25 = FALSE
    guard_24 = TRUE
    guard_23 = FALSE
    guard_22 = FALSE
    guard_21 = FALSE
    guard_20 = FALSE
    guard_19 = FALSE
    guard_18 = FALSE
    guard_17 = FALSE
    guard_16 = FALSE
    guard_15 = FALSE
    guard_14 = FALSE
    guard_13 = FALSE
    guard_12 = FALSE
    guard_11 = FALSE
    guard_10 = FALSE
    guard_9 = FALSE
    guard_8 = FALSE
    guard_7 = FALSE
    guard_6 = FALSE
    guard_5 = FALSE
    guard_4 = FALSE
    guard_3 = FALSE
    guard_2 = FALSE
    guard_1 = FALSE
    guard_0 = FALSE
    counterstrategy_act_19 = FALSE
    counterstrategy_act_18 = FALSE
    counterstrategy_act_17 = FALSE
    counterstrategy_act_16 = FALSE
    counterstrategy_act_15 = FALSE
    counterstrategy_act_14 = FALSE
    counterstrategy_act_13 = TRUE
    counterstrategy_act_12 = FALSE
    counterstrategy_act_11 = FALSE
    counterstrategy_act_10 = FALSE
    counterstrategy_act_9 = TRUE
    counterstrategy_act_8 = FALSE
    counterstrategy_act_7 = FALSE
    counterstrategy_act_6 = FALSE
    counterstrategy_act_5 = FALSE
    counterstrategy_act_4 = FALSE
    counterstrategy_act_3 = FALSE
    counterstrategy_act_2 = FALSE
    counterstrategy_act_1 = FALSE
    counterstrategy_act_0 = FALSE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_26 = FALSE
    act_25 = FALSE
    act_24 = TRUE
    act_23 = FALSE
    act_22 = FALSE
    act_21 = FALSE
    act_20 = FALSE
    act_19 = FALSE
    act_18 = FALSE
    act_17 = FALSE
    act_16 = FALSE
    act_15 = FALSE
    act_14 = FALSE
    act_13 = FALSE
    act_12 = FALSE
    act_11 = FALSE
    act_10 = FALSE
    act_9 = FALSE
    act_8 = FALSE
    act_7 = FALSE
    act_6 = FALSE
    act_5 = FALSE
    act_4 = FALSE
    act_3 = FALSE
    act_2 = FALSE
    act_1 = FALSE
    act_0 = FALSE
  -> State: 1.2 <-
    cr_prev = 0
    empty_l = TRUE
    empty_r = TRUE
    turn = mon_env
    counterstrategy_guard_5 = TRUE
    guard_27 = TRUE
    guard_24 = FALSE
    counterstrategy_act_13 = FALSE
    counterstrategy_act_9 = FALSE
    counterstrategy_act_5 = TRUE
    identity_counterstrategy = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_24 = FALSE
    act_8 = TRUE
  -> State: 1.3 <-
    empty_l = FALSE
    empty_r = FALSE
    exit_l = TRUE
    exit_r = TRUE
    stop_l = TRUE
    stop_r = FALSE
    turn = con
    mon_empty_l = FALSE
    mon_empty_r = FALSE
    st_2_0 = TRUE
    st__10_0 = FALSE
    counterstrategy_guard_5 = FALSE
    identity_counterstrategy = TRUE
  -> State: 1.4 <-
    turn = mon_con
    counterstrategy_guard_11 = TRUE
    counterstrategy_act_11 = TRUE
    counterstrategy_act_5 = FALSE
    identity_counterstrategy = FALSE
  -> State: 1.5 <-
    entry_r = TRUE
    exit_l = FALSE
    stop_l = FALSE
    turn = env
    mon_empty_l = TRUE
    pred_____MINUS_3_MULT_cr__PLUS_1__GT__EQ_0_ = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = TRUE
    pred__cr_LT__EQ_0_ = FALSE
    st_2_0 = FALSE
    st__5_0 = TRUE
    st_18_0_seen_once = TRUE
    counterstrategy_guard_11 = FALSE
    guard_27 = FALSE
    guard_17 = TRUE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_17 = TRUE
    act_8 = FALSE
  -> State: 1.6 <-
    cr = 1
    empty_l = TRUE
    turn = mon_env
    st_18_0_seen_once = FALSE
    counterstrategy_guard_0 = TRUE
    guard_27 = TRUE
    guard_17 = FALSE
    counterstrategy_act_11 = FALSE
    counterstrategy_act_2 = TRUE
    counterstrategy_act_0 = TRUE
    identity_counterstrategy = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_17 = FALSE
    act_8 = TRUE
  -> State: 1.7 <-
    empty_l = FALSE
    entry_l = TRUE
    l2r = FALSE
    stop_l = TRUE
    turn = con
    mon_empty_l = FALSE
    pred_____MINUS_3_MULT_crprev__PLUS_1__GT____MINUS_3_MULT_cr__PLUS_1__ = FALSE
    st_17_0 = TRUE
    st__5_0 = FALSE
    counterstrategy_guard_0 = FALSE
    identity_counterstrategy = TRUE
  -> State: 1.8 <-
    cr_prev = 1
    turn = mon_con
    counterstrategy_guard_17 = TRUE
    counterstrategy_act_17 = TRUE
    counterstrategy_act_2 = FALSE
    counterstrategy_act_0 = FALSE
    identity_counterstrategy = FALSE
  -> State: 1.9 <-
    entry_l = FALSE
    entry_r = FALSE
    exit_l = TRUE
    l2r = TRUE
    stop_l = FALSE
    stop_r = TRUE
    turn = env
    mon_empty_l = TRUE
    pred_____MINUS_3_MULT_crprev__PLUS_1__LT____MINUS_3_MULT_cr__PLUS_1__ = TRUE
    st_17_0 = FALSE
    st__7_0 = TRUE
    counterstrategy_guard_17 = FALSE
    guard_27 = FALSE
    guard_22 = TRUE
    identity_counterstrategy = TRUE
    act_27 = FALSE
    identity_eventually__allow_grant = FALSE
    act_22 = TRUE
    act_8 = FALSE
  -> State: 1.10 <-
    cr = 0
    empty_l = TRUE
    empty_r = TRUE
    turn = mon_env
    compatible_state_predicates = FALSE
    compatible = FALSE
    compatible_outputs = FALSE
    counterstrategy_guard_2 = TRUE
    guard_27 = TRUE
    guard_22 = FALSE
    act_27 = TRUE
    identity_eventually__allow_grant = TRUE
    act_22 = FALSE
    act_8 = TRUE
  -> State: 1.11 <-
    empty_l = FALSE
    empty_r = FALSE
    mismatch = TRUE
  -- Loop starts here
  -> State: 1.12 <-
    cr_prev = -1
    compatible_tran_predicates = FALSE
  -> State: 1.13 <-
  -> State: 1.14 <-"""

def write_counterexample_print(program,
                               agreed_on_transitions,
                               disagreed_on_state):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print("\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))
        print(("env: " if "env" == state["turn"] else "con: ") + str(trans))

    print("Environment wanted state to satisfy:")

    print(", ".join([str(p) for p in disagreed_on_state[0]]))

    print("Program however has state:")
    print(", ".join([v + " = " + k for v, k in disagreed_on_state[1].items()]))
