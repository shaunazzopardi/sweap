import logging

from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import (
    StatePredicate,
)
from analysis.abstraction.effects_abstraction.predicates.TransitionPredicate import (
    TransitionPredicate,
)
from config import Config
from analysis.abstraction.concretisation import concretize_transitions
from analysis.abstraction.interface.ltl_abstraction_type import (
    LTLAbstractionType,
)
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from analysis.model_checker import ModelChecker
from programs.program import Program
from programs.util import parse_nuxmv_ce_output_finite
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, label_pred, stringify_pred
from prop_lang.variable import Variable
from synthesis.mealy_machine import MealyMachine
from synthesis.moore_machine import MooreMachine


def compatibility_checking_con(
    program: Program,
    predicate_abstraction: EffectsAbstraction,
    mealy_machine: MealyMachine,
    original_ltl_spec,
):
    moore_nuxmv = mealy_machine.to_nuXmv_with_turns_for_con_verif(
        predicate_abstraction.get_program().bin_state_vars,
        predicate_abstraction.get_program().out_events,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
    )

    all_preds = predicate_abstraction.get_all_preds()

    system = create_nuxmv_model_for_compatibility_checking(
        program,
        moore_nuxmv,
        all_preds,
        predicate_abstraction.v_to_chain_pred.values(),
        not program.deterministic,
        not program.deterministic,
        predicate_mismatch=True,
        prefer_lassos=False,
    )
    logging.info(system)
    print(
        "Verifying whether controller enforces required LTL specification on program.."
    )
    bound = 50
    (
        contradictory,
        there_is_mismatch,
        out,
    ) = there_is_mismatch_between_program_and_controller(
        system, original_ltl_spec, bound
    )

    if contradictory:
        raise Exception(
            "I have no idea what's gone wrong. Strix thinks the previous mealy machine is a "
            + ("controller" if True else "counterstrategy")
            + ", but nuxmv thinks it is non consistent with the program.\n"
            + "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division."
        )

    if there_is_mismatch:
        if "Maximum bound reached" in out:
            print(
                "Controller correct up to "
                + str(bound)
                + " IC3 steps, I do not verify beyond this."
            )
            return True
        logging.info(out)
        logging.info(str(mealy_machine))
        print(str(mealy_machine))
        raise Exception(
            "Controller does not enforce the required LTL property on the program:\n"
            + str(out)
        )
    else:
        print(out)
        print("Controller enforces the required LTL property!")
        return True


def create_nuxmv_model_for_compatibility_checking(
    program: Program,
    strategy_model: NuXmvModel,
    pred_list,
    chain_preds,
    include_mismatches_due_to_nondeterminism=False,
    colloborate=False,
    predicate_mismatch=False,
    prefer_lassos=False,
):
    program_model = program.to_nuXmv_with_turns_for_con_verif()
    bool_preds = [p.bool_var for p in pred_list if isinstance(p, StatePredicate)]
    bool_preds.extend(
        [
            t
            for p in pred_list
            if isinstance(p, TransitionPredicate)
            for t in p.bool_rep.values()
        ]
    )

    text = "MODULE main\n"

    vars = (
        sorted(program_model.vars)
        + sorted([v for v in strategy_model.vars if v not in program_model.vars])
        + ["init_state : boolean"]
    )
    text += "VAR\n" + "\t" + ";\n\t".join(vars) + ";\n"

    pred_rep_to_val = {}
    binned_preds = []
    for ch_p in chain_preds:
        for p, rep in ch_p.bin_rep.items():
            bool_rep = stringify_pred(p).name
            pred_rep_to_val[bool_rep] = p
            binned_preds.append(bool_rep + " := " + str(rep))
    text += (
        "DEFINE\n"
        + "\t"
        + ";\n\t".join(program_model.define + strategy_model.define + binned_preds)
        + ";\n"
    )

    safety_predicate_truth = [
        BiOp(p.pred, "<->", p.bool_var)
        for p in pred_list
        if isinstance(p, StatePredicate)
    ]

    safety_predicate_truth += [
        BiOp(bool_rep, "<->", (p)) for bool_rep, p in pred_rep_to_val.items()
    ]

    tran_predicate_truth = [
        BiOp(pred, "<->", bool_var)
        for p in pred_list
        if isinstance(p, TransitionPredicate)
        for pred, bool_var in p.bool_rep.items()
    ]

    prog_output_equality = [
        BiOp(o, "=", Variable("prog_" + o.name)) for o in program.out_events
    ]

    prog_state_equality = [
        BiOp(Variable(s), "=", program.states_binary_map[s]) for s in program.states
    ]

    compatible_output = (
        "\tcompatible_outputs := "
        + "(("
        + str(conjunct_formula_set(prog_output_equality))
        + "))"
        + ";\n"
    )
    compatible_states = (
        "\tcompatible_states := "
        + "(("
        + str(conjunct_formula_set(prog_state_equality))
        + "))"
        + ";\n"
    )
    compatible_state_predicates = (
        "\tcompatible_state_predicates := "
        + "(("
        + str(conjunct_formula_set(safety_predicate_truth))
        + "))"
        + ";\n"
    )
    # TODO there is something wrong when refining abstract counterstrategy into env - con steps, the transition predicates are not being computed correctly
    compatible_tran_predicates = (
        "\tcompatible_tran_predicates := "
        + "((!init_state) -> ("
        + str(conjunct_formula_set(tran_predicate_truth))
        + "))"
        + ";\n"
    )
    compatible = (
        "\tcompatible := "
        + (
            "compatible_state_predicates & compatible_tran_predicates & "
            if predicate_mismatch
            else ""
        )
        + "compatible_outputs & compatible_states"
        + ";\n"
    )

    text += (
        compatible_output
        + compatible_states
        + compatible
        + compatible_state_predicates
        + compatible_tran_predicates
    )

    # TODO consider adding checks that state predicates expected by env are true, for debugging predicate abstraction

    text += (
        "INIT\n"
        + "\t("
        + ")\n\t& (".join(
            program_model.init + strategy_model.init + ["init_state = TRUE"]
        )
        + ")\n"
    )
    text += (
        "INVAR\n"
        + "\t(("
        + ")\n\t& (".join(program_model.invar + strategy_model.invar)
        + "))\n"
    )

    turn_logic = ["!next(init_state)"]

    new_trans = program_model.trans + strategy_model.trans + turn_logic
    normal_trans = "\t((" + ")\n\t& (".join(new_trans) + "))\n"

    text += "TRANS\n" + normal_trans + "\n"

    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text


def create_nuxmv_model(nuxmvModel):
    from warnings import warn

    warn("This method is deprecated.", DeprecationWarning, stacklevel=2)

    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(nuxmvModel.vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(nuxmvModel.define) + ";\n"
    text += "INIT\n" + "\t(" + ")\n\t& (".join(nuxmvModel.init + ["turn = env"]) + ")\n"
    text += "INVAR\n" + "\t(" + ")\n\t& (".join(nuxmvModel.invar) + ")\n"

    turn_logic = ["(turn = con -> next(turn) = prog_con)"]
    turn_logic += ["(turn = env -> next(turn) = prog_env)"]
    turn_logic += ["(turn = prog_env -> next(turn) = con)"]
    turn_logic += ["(turn = prog_con -> next(turn) = env)"]

    text += "TRANS\n" + "\t(" + ")\n\t& (".join(nuxmvModel.trans + turn_logic) + ")\n"
    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text


def there_is_mismatch_between_program_and_strategy(
    system, controller: bool, mismatch_condition=None
):
    model_checker = ModelChecker()
    config = Config.getConfig()
    if config.debug:
        logging.info(system)
        # Sanity check
        result, out = model_checker.invar_check(system, "F FALSE", None, True)
        if result:
            logging.info("Are you sure the counterstrategy given is complete?")
            return True, None, out

    if not controller:
        if mismatch_condition is None:
            there_is_no_mismatch, out = model_checker.invar_check(
                system, "compatible", None, config.mc
            )
        else:
            there_is_no_mismatch, out = model_checker.invar_check(
                system,
                "!(!compatible" + " & " + mismatch_condition + ")",
                None,
                config.mc,
            )
            if there_is_no_mismatch:
                there_is_no_mismatch, out = model_checker.invar_check(
                    system, "compatible", None, config.mc
                )

        return False, not there_is_no_mismatch, out
    else:
        return False, False, None


def there_is_mismatch_between_program_and_controller(system, ltlspec, bound):
    model_checker = ModelChecker()
    config = Config.getConfig()
    logging.info(system)
    # Sanity check
    result, out = model_checker.invar_check(system, "F FALSE", None, True)
    if result:
        logging.info("Are you sure the controller given is complete?")
        return True, False, None

    there_is_no_mismatch, out = model_checker.invar_check(
        system,
        "(G(compatible)) -> (" + str(ltlspec.to_nuxmv()) + ")",
        10,
        True,
    )
    return False, not there_is_no_mismatch, out
