import time
import logging

from analysis.compatibility_checking.compatibility_checking import compatibility_checking
from analysis.refinement.fairness_refinement.fairness_util import try_liveness_refinement
from analysis.refinement.safety_refinement.interpolation_refinement import safety_refinement_seq_int


def refinement_standard(program,
                        predicate_abstraction,
                        mm,
                        real,
                        base_abstraction,
                        ltlAbstractionType,
                        loop_counter,
                        #TODO put all the below parameters in a dictionary
                        project_on_abstraction,
                        prefer_lasso_counterexamples,
                        allow_user_input,
                        keep_only_bool_interpolants,
                        conservative_with_state_predicates,
                        eager,
                        only_safety):
    start = time.time()

    print("checking for compatibility of counterstrategy with program")
    determination, result = compatibility_checking(program,
                                                   predicate_abstraction,
                                                   mm,
                                                   real,
                                                   base_abstraction,
                                                   ltlAbstractionType,
                                                   project_on_abstraction,
                                                   prefer_lasso_counterexamples)

    logging.info("compatibility checking took " + str(time.time() - start))

    if determination == False:
        logging.info("Problem is unrealisable.")
        return True, mm
    elif determination == True:
        raise Exception("error")
    else:
        agreed_on_execution, disagreed_on_state = result

    # write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)
    if not only_safety:
        ## try fairness refinement
        start = time.time()
        print("trying fairness refinement")
        success, result = try_liveness_refinement(mm,
                                                  program,
                                                  predicate_abstraction,
                                                  agreed_on_execution,
                                                  disagreed_on_state,
                                                  loop_counter,
                                                  allow_user_input)

        logging.info("liveness refinement took " + str(time.time() - start))
    else:
        success = False
        result = None

    if success:
        loop_counter = loop_counter + 1
        (new_state_preds, new_tran_preds), new_ltl_constraints = result
    else:
        new_state_preds = set()
        new_tran_preds = set()
        new_ltl_constraints = set()

    if eager or (not success and result is None):
        ## do safety refinement
        start = time.time()
        print("trying safety refinement")
        success, result = safety_refinement_seq_int(program,
                                                    predicate_abstraction,
                                                    agreed_on_execution,
                                                    disagreed_on_state,
                                                    allow_user_input,
                                                    keep_only_bool_interpolants,
                                                    conservative_with_state_predicates)

        logging.info("safety refinement took " + str(time.time() - start))
        if success:
            new_state_preds.update(result)
        else:
            raise Exception("Could not find any new state predicates.")

    return False, ((new_state_preds, new_tran_preds), new_ltl_constraints, loop_counter)