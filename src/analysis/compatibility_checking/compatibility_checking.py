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
from synthesis.moore_machine import MooreMachine


def compatibility_checking(
    program: Program,
    predicate_abstraction: EffectsAbstraction,
    moore_machine: MooreMachine,
    is_controller: bool,
    base_abstraction,
    ltlAbstractionType: LTLAbstractionType,
    project_on_abstraction: bool,
    prefer_lasso_counterexamples: bool,
):
    moore_nuxmv = moore_machine.to_nuXmv_with_turns(
        predicate_abstraction.get_program().bin_state_vars,
        predicate_abstraction.get_program().out_events,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
    )

    if prefer_lasso_counterexamples:
        # try looking for a lasso mismatch first
        strategy_states = sorted(
            [
                "("
                + str(s).split(" : ")[0]
                + " & "
                + str(s).split(" : ")[0]
                + "_seen_more_than_once)"
                for s in moore_nuxmv.vars
                if str(s).startswith("st_")
            ]
        )
        lasso_mismatch = "(" + " | ".join(strategy_states) + ")"

        mismatch_condition = "!mismatch &" + lasso_mismatch
    else:
        mismatch_condition = None

    all_preds = predicate_abstraction.get_all_preds()
    symbol_table = predicate_abstraction.get_symbol_table()

    system = create_nuxmv_model_for_compatibility_checking(
        program,
        moore_nuxmv,
        all_preds,
        predicate_abstraction.v_to_chain_pred.values(),
        not program.deterministic,
        not program.deterministic,
        predicate_mismatch=True,
        prefer_lassos=prefer_lasso_counterexamples,
    )
    logging.info(system)
    (
        contradictory,
        there_is_mismatch,
        out,
    ) = there_is_mismatch_between_program_and_strategy(
        system, is_controller, mismatch_condition=mismatch_condition
    )

    if contradictory:
        raise Exception(
            "I have no idea what's gone wrong. Strix thinks the previous mealy machine is a "
            + ("controller" if is_controller else "counterstrategy")
            + ", but nuxmv thinks it is non consistent with the program.\n"
            + "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division."
        )

    if not there_is_mismatch:
        logging.info("No mismatch found.")

        ## Finished
        if project_on_abstraction:
            logging.info(
                "Computing projection of "
                + ("strategy" if is_controller else "counterstrategy")
                + " onto predicate abstraction.."
            )
            controller_projected_on_program = (
                moore_machine.project_controller_on_program(
                    ("strategy" if is_controller else "counterstrategy"),
                    program,
                    predicate_abstraction,
                    symbol_table,
                )
            )

            for t in (
                controller_projected_on_program.con_transitions
                + controller_projected_on_program.transitions
            ):
                ok = False
                for tt in (
                    controller_projected_on_program.con_transitions
                    + controller_projected_on_program.transitions
                ):
                    if t.tgt == tt.src:
                        ok = True
                        break

                if not ok:
                    logging.info(controller_projected_on_program.to_dot())

                    raise Exception(
                        "Warning: Model checking says counterstrategy is fine, but something has gone wrong with projection "
                        "onto the predicate abstraction, and I have no idea why. "
                        "The "
                        + ("controller" if is_controller else "counterstrategy")
                        + " has no outgoing transition from this program state: "
                        + ", ".join([str(p) for p in list(t.tgt)])
                    )
            result = controller_projected_on_program.to_dot()
        else:
            result = moore_machine.to_dot(all_preds)

        if is_controller:
            return True, result
        else:
            # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
            return False, result

    logging.info(out)
    ## Compute mismatch trace
    cs_alphabet = [v.split(":")[0].strip() for v in moore_nuxmv.vars]
    (
        agreed_on_transitions_indexed,
        incompatible_state,
    ) = parse_nuxmv_ce_output_finite(program, out, cs_alphabet)
    agreed_on_execution, disagreed_on_state = concretize_transitions(
        program, agreed_on_transitions_indexed, incompatible_state
    )

    return None, (agreed_on_execution, disagreed_on_state)


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
    program_model = program.to_nuXmv_with_turns()
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
    strategy_states = sorted(
        [
            v
            for v in strategy_model.vars
            if v not in program_model.vars and str(v).startswith("st_")
        ]
    )
    seen_strategy_states_decs = [
        str(s).replace(" : ", "_seen_once : ") for s in strategy_states
    ]
    seen_strategy_states_decs += [
        str(s).replace(" : ", "_seen_more_than_once : ") for s in strategy_states
    ]

    vars = (
        sorted(program_model.vars)
        + sorted([s + ": boolean" for s in program.states])
        + sorted([v for v in strategy_model.vars if v not in program_model.vars])
        + (seen_strategy_states_decs if prefer_lassos else [])
        + ["mismatch : boolean"]
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
        + "((turn == cs) -> ("
        + str(conjunct_formula_set(prog_output_equality))
        + "))"
        + ";\n"
    )
    compatible_states = (
        "\tcompatible_states := "
        + "((turn == cs) -> ("
        + str(conjunct_formula_set(prog_state_equality))
        + "))"
        + ";\n"
    )
    compatible_state_predicates = (
        "\tcompatible_state_predicates := "
        + "((turn == cs) -> ("
        + str(conjunct_formula_set(safety_predicate_truth))
        + "))"
        + ";\n"
    )
    # TODO there is something wrong when refining abstract counterstrategy into env - con steps, the transition predicates are not being computed correctly
    compatible_tran_predicates = (
        "\tcompatible_tran_predicates := "
        + "((!init_state && turn == cs) -> ("
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
            program_model.init
            + strategy_model.init
            + ["turn = cs", "mismatch = FALSE", "init_state = TRUE"]
            + (
                (
                    (
                        [
                            s.split(" : ")[0] + "_seen_once = FALSE"
                            for s in strategy_states
                        ]
                        + [
                            s.split(" : ")[0] + "_seen_more_than_once = FALSE"
                            for s in strategy_states
                        ]
                    )
                )
                if prefer_lassos
                else []
            )
        )
        + ")\n"
    )
    text += (
        "INVAR\n"
        + "\t(("
        + ")\n\t& (".join(program_model.invar + strategy_model.invar)
        + "))\n"
    )

    turn_logic = ["(turn = prog -> (!next(init_state) && next(turn) = cs))"]
    turn_logic += ["(turn = cs -> (!next(init_state) && next(turn) = prog))"]

    maintain_prog_vars = str(
        conjunct_formula_set(
            [
                BiOp(
                    UniOp("next", Variable("prog_" + str(m))),
                    " = ",
                    Variable("prog_" + str(m)),
                )
                for m in (program.out_events)
            ]
            + [
                BiOp(UniOp("next", Variable(str(m))), " = ", Variable(str(m)))
                for m in program.bin_state_vars + bool_preds
            ]
        )
    )
    new_trans = (
        ["compatible", "!next(mismatch)"]
        + program_model.trans
        + strategy_model.trans
        + turn_logic
    )
    normal_trans = "\t((" + ")\n\t& (".join(new_trans) + "))\n"

    normal_trans += (
        "\t | (!compatible & "
        + " next(mismatch) & identity_"
        + program_model.name
        + " & identity_"
        + strategy_model.name
        + " & next(turn) = turn & "
        + maintain_prog_vars
        + ")"
    )
    normal_trans = "(!mismatch -> (" + normal_trans + "))"

    deadlock = (
        "(mismatch -> (next(mismatch) & identity_"
        + program_model.name
        + " & identity_"
        + strategy_model.name
        + " & next(turn) = turn & "
        + maintain_prog_vars
        + "))"
    )

    text += "TRANS\n" + normal_trans + "\n\t& " + deadlock + "\n"

    if prefer_lassos:
        report_if_state_seen = "\n\t& ".join(
            [
                "((((turn == cs) & "
                + s.split(" : ")[0]
                + ") "
                + " | "
                + s.split(" : ")[0]
                + "_seen_once) "
                + "<-> next("
                + s.split(" : ")[0]
                + "_seen_once))"
                for s in strategy_states
            ]
        )

        report_if_state_seen += "\n\t& " + "\n\t& ".join(
            [
                "((("
                + ("(turn == cs)")
                + " & "
                + s.split(" : ")[0]
                + " & "
                + s.split(" : ")[0]
                + "_seen_once "
                + ") "
                + " | "
                + s.split(" : ")[0]
                + "_seen_more_than_once) "
                + "<-> next("
                + s.split(" : ")[0]
                + "_seen_more_than_once))"
                for s in strategy_states
            ]
        )

        text += "\t&" + report_if_state_seen + "\n"

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
