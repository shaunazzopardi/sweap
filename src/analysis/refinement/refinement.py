import logging
import time

import config
from analysis.compatibility_checking.compatibility_checking import (
    compatibility_checking,
)
from analysis.refinement.fairness_refinement.fairness_util import (
    try_liveness_refinement,
)
from analysis.refinement.safety_refinement.interpolation_refinement import (
    safety_refinement_seq_int,
)


def refinement_standard(
    program,
    predicate_abstraction,
    mm,
    real,
    signatures,
    loop_counter,
    # TODO put all the below parameters in a dictionary
    prefer_lasso_counterexamples,
    allow_user_input,
):
    start = time.time()

    print("checking for compatibility with program")
    determination, result = compatibility_checking(
        program,
        predicate_abstraction,
        mm,
        real,
        prefer_lasso_counterexamples,
    )

    logging.info("compatibility checking took " + str(time.time() - start))
    dual = config.Config.getConfig().dual
    if determination == True:
        if dual:
            logging.info("Problem is realisable.")
        else:
            logging.info("Problem is unrealisable.")
        return True, mm
    else:
        agreed_on_execution, disagreed_on_state = result

    write_counterexample_state(program, agreed_on_execution, disagreed_on_state)
    ## try fairness refinement
    start = time.time()
    print("trying fairness refinement")
    success, result = try_liveness_refinement(
        mm,
        program,
        predicate_abstraction,
        agreed_on_execution,
        disagreed_on_state,
        signatures,
        loop_counter,
        allow_user_input,
    )

    logging.info("liveness refinement took " + str(time.time() - start))

    if success:
        loop_counter = loop_counter + 1
        if result[0] is None:
            (
                new_state_preds,
                new_tran_preds,
            ), new_structural_loop_constraints = result[1]
            new_ltl_constraints = set()
        elif result[1] is None:
            (new_state_preds, new_tran_preds), new_ltl_constraints = result[0]
            new_structural_loop_constraints = set()
        else:
            raise Exception("Expected success to be true")
    else:
        new_state_preds = set()
        new_tran_preds = set()
        new_ltl_constraints = set()
        new_structural_loop_constraints = set()

    if not success:
        ## do safety refinement
        start = time.time()
        print("trying safety refinement")
        success, result = safety_refinement_seq_int(
            program,
            predicate_abstraction,
            agreed_on_execution,
            disagreed_on_state,
            signatures,
            allow_user_input,
        )

        logging.info("safety refinement took " + str(time.time() - start))
        if success:
            result = [
                p
                for p in result
                if not (
                    p in predicate_abstraction.state_predicates
                    or p in predicate_abstraction.chain_state_predicates
                )
            ]
            # TODO why is there sometimes a predicate we already know? is abstraction not presice enough?
            if len(result) == 0:
                raise Exception(
                    "Safety refinement returned already known state predicates."
                )
            new_state_preds.update(result)
        else:
            raise Exception("Could not find any new state predicates.")

    return False, (
        (new_state_preds, new_tran_preds),
        new_ltl_constraints,
        new_structural_loop_constraints,
        loop_counter,
    )


def write_counterexample_state(
    program,
    agreed_on_transitions,
    disagreed_on_state,
):
    logging.info("Mismatch:")
    logging.info("Agreed on transitions:")
    for t, prog_state, machine_state in agreed_on_transitions:
        state = prog_state | machine_state
        vs = set(
            t.condition.variablesin()
            + [v for v in list(state.keys()) if str(v).startswith("mon_")]
            + [v for v in list(state.keys()) if str(v).startswith("pred_")]
            + [v for v in program.env_events + program.con_events]
        )

        logging.info(
            "var values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs])
        )
        logging.info(("env: " if "env" == state["turn"] else "con: ") + str(t))

    logging.info("Environment wanted state to satisfy:")

    logging.info(", ".join([str(p) for p in disagreed_on_state[0]]))

    logging.info("Program however has state:")
    logging.info(
        ", ".join([v + " = " + k for v, k in disagreed_on_state[1][1].items()])
    )
