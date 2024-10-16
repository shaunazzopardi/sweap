import logging

from config import Config
from analysis.abstraction.concretisation import concretize_transitions
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionType
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.compatibility_checking.nuxmv_model import NuXmvModel
from analysis.model_checker import ModelChecker
from programs.program import Program
from synthesis.mealy_machine import MealyMachine
from programs.util import parse_nuxmv_ce_output_finite
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, label_pred
from prop_lang.variable import Variable


def compatibility_checking(program: Program,
                           predicate_abstraction: PredicateAbstraction,
                           mealy_machine: MealyMachine,
                           is_controller: bool,
                           base_abstraction,
                           ltlAbstractionType: LTLAbstractionType,
                           prog_events,
                           project_on_abstraction: bool,
                           prefer_lasso_counterexamples: bool):
    mealy_nuxmv = mealy_machine.to_nuXmv_with_turns(predicate_abstraction.get_program().states,
                                                    predicate_abstraction.get_program().out_events,
                                                    predicate_abstraction.get_state_predicates(),
                                                    predicate_abstraction.get_transition_predicates())

    if prefer_lasso_counterexamples:
        # try looking for a lasso mismatch first
        strategy_states = sorted(
            ["(" + str(s).split(" : ")[0] + " & " + str(s).split(" : ")[0] + "_seen_more_than_once)" for s in
             mealy_nuxmv.vars
             if str(s).startswith("st_")])
        lasso_mismatch = "(" + " | ".join(strategy_states) + ")"

        mismatch_condition = "!mismatch &" + lasso_mismatch
    else:
        mismatch_condition = None

    all_preds = predicate_abstraction.get_all_preds()
    symbol_table = predicate_abstraction.get_symbol_table()

    system = create_nuxmv_model_for_compatibility_checking(program,
                                                           mealy_nuxmv,
                                                           prog_events,
                                                           all_preds,
                                                           not program.deterministic,
                                                           not program.deterministic,
                                                           predicate_mismatch=True,
                                                           prefer_lassos=prefer_lasso_counterexamples)
    logging.info(system)
    contradictory, there_is_mismatch, out = there_is_mismatch_between_program_and_strategy(system,
                                                                                           is_controller,
                                                                                           mismatch_condition=mismatch_condition)

    if contradictory:
        raise Exception("I have no idea what's gone wrong. Strix thinks the previous mealy machine is a " +
                        ("controller" if is_controller else "counterstrategy") +
                        ", but nuxmv thinks it is non consistent with the program.\n" +
                        "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division.")

    if not there_is_mismatch:
        logging.info("No mismatch found.")

        ## Finished
        if project_on_abstraction:
            logging.info("Computing projection of " + (
                "strategy" if is_controller else "counterstrategy") + " onto predicate abstraction..")
            controller_projected_on_program = mealy_machine.project_controller_on_program((
                "strategy" if is_controller else "counterstrategy"),
                program,
                predicate_abstraction,
                symbol_table)

            for t in controller_projected_on_program.con_transitions + controller_projected_on_program.transitions:
                ok = False
                for tt in controller_projected_on_program.con_transitions + controller_projected_on_program.transitions:
                    if t.tgt == tt.src:
                        ok = True
                        break

                if not ok:
                    logging.info(controller_projected_on_program.to_dot())

                    raise Exception(
                        "Warning: Model checking says counterstrategy is fine, but something has gone wrong with projection "
                        "onto the predicate abstraction, and I have no idea why. "
                        "The " + (
                            "controller" if is_controller else "counterstrategy") + " has no outgoing transition from this program state: "
                        + ", ".join([str(p) for p in list(t.tgt)]))
            result = controller_projected_on_program.to_dot()
        else:
            result = mealy_machine.to_dot(all_preds)

        if is_controller:
            return True, result
        else:
            # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
            return False, result

    logging.info(out)
    ## Compute mismatch trace
    cs_alphabet = [v.split(":")[0].strip() for v in mealy_nuxmv.vars]
    agreed_on_transitions_indexed, incompatible_state = parse_nuxmv_ce_output_finite(
        program, out, cs_alphabet)
    agreed_on_execution, disagreed_on_state = concretize_transitions(program,
                                                                     agreed_on_transitions_indexed,
                                                                     incompatible_state)

    return None, (agreed_on_execution, disagreed_on_state)


def create_nuxmv_model_for_compatibility_checking(program : Program, strategy_model: NuXmvModel, prog_events,
                                                  pred_list, include_mismatches_due_to_nondeterminism=False,
                                                  colloborate=False, predicate_mismatch=False, prefer_lassos=False):
    pred_definitions = {label_pred(p, pred_list): p for p in pred_list}
    program_model = program.to_nuXmv_with_turns(include_mismatches_due_to_nondeterminism, colloborate, pred_definitions)

    text = "MODULE main\n"
    strategy_states = sorted([v for v in strategy_model.vars
                              if v not in program_model.vars and str(v).startswith("st_")])
    seen_strategy_states_decs = [str(s).replace(" : ", "_seen_once : ") for s in strategy_states]
    seen_strategy_states_decs += [str(s).replace(" : ", "_seen_more_than_once : ") for s in strategy_states]

    vars = sorted(program_model.vars) \
           + sorted([v for v in strategy_model.vars
                     if v not in program_model.vars]) \
           + seen_strategy_states_decs \
           + ["mismatch : boolean"] \
           + ["init_state : boolean"]
    text += "VAR\n" + "\t" + ";\n\t".join(vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(program_model.define + strategy_model.define) + ";\n"

    safety_predicate_truth = [BiOp(label_pred(p, pred_list), '<->', p)
                              for p in pred_list if not any([v for v in p.variablesin() if "_prev" in str(
            v)])]

    tran_predicate_truth = [BiOp(label_pred(p, pred_list), '<->', p)
                            for p in pred_list if any([v for v in p.variablesin() if "_prev" in str(
            v)])]

    prog_output_equality = [BiOp(o, '=', Variable("prog_" + o.name))
                           for o in program.out_events]

    prog_state_equality = [BiOp(Variable(s), '=', Variable("prog_" + s))
                          for s in program.states]

    compatible_output = "\tcompatible_outputs := " + "((turn == cs) -> (" + str(
        conjunct_formula_set(prog_output_equality)) + "))" + ";\n"
    compatible_states = "\tcompatible_states := " + "((turn == cs) -> (" + str(
        conjunct_formula_set(prog_state_equality)) + "))" + ";\n"
    compatible_state_predicates = "\tcompatible_state_predicates := " + "((turn == cs) -> (" + str(
        conjunct_formula_set(safety_predicate_truth)) + "))" + ";\n"
    # TODO there is something wrong when refining abstract counterstrategy into env - con steps, the transition predicates are not being computed correctly
    compatible_tran_predicates = "\tcompatible_tran_predicates := " + "((!init_state && turn == cs) -> (" + str(
        conjunct_formula_set(tran_predicate_truth)) + "))" + ";\n"
    compatible = "\tcompatible := " + (
        "compatible_state_predicates & compatible_tran_predicates & " if predicate_mismatch else "") + "compatible_outputs & compatible_states" + ";\n"

    text += compatible_output + compatible_states + compatible + compatible_state_predicates + compatible_tran_predicates

    # TODO consider adding checks that state predicates expected by env are true, for debugging predicate abstraction

    text += "INIT\n" + "\t(" + ")\n\t& (".join(
        program_model.init + strategy_model.init + ["turn = cs", "mismatch = FALSE", "init_state = TRUE"] +
        ((([s.split(" : ")[0] + "_seen_once = FALSE" for s in strategy_states] +
           [s.split(" : ")[0] + "_seen_more_than_once = FALSE" for s in
            strategy_states])) if prefer_lassos else [])) + ")\n"
    text += "INVAR\n" + "\t((" + ")\n\t& (".join(program_model.invar + strategy_model.invar) + "))\n"

    turn_logic = ["(turn = prog -> (!next(init_state) && next(turn) = cs))"]
    turn_logic += ["(turn = cs -> (!next(init_state) && next(turn) = prog))"]

    maintain_prog_vars = str(conjunct_formula_set(
        [BiOp(UniOp("next", Variable("prog_" + m.name)), ' = ', Variable("prog_" + m.name)) for m in (prog_events)]
        + [BiOp(UniOp("next", Variable(m.name)), ' = ', Variable(m.name)) for m in
           [label_pred(p, pred_list) for p in pred_list]]))
    new_trans = ["compatible", "!next(mismatch)"] + program_model.trans + strategy_model.trans + turn_logic
    normal_trans = "\t((" + ")\n\t& (".join(new_trans) + "))\n"

    normal_trans += "\t | (!compatible & " + \
                    " next(mismatch) & identity_" + program_model.name + \
                    " & identity_" + strategy_model.name + " & next(turn) = turn & " + maintain_prog_vars + ")"
    normal_trans = "(!mismatch -> (" + normal_trans + "))"

    deadlock = "(mismatch -> (next(mismatch) & identity_" + program_model.name + " & identity_" + strategy_model.name + " & next(turn) = turn & " + maintain_prog_vars + "))"

    text += "TRANS\n" + normal_trans + "\n\t& " + deadlock + "\n"

    if prefer_lassos:
        report_if_state_seen = \
            "\n\t& ".join(["((((turn == cs) & " + s.split(" : ")[0]
                           + ") " + " | " + s.split(" : ")[0] + "_seen_once) " +
                           "<-> next(" + s.split(" : ")[0] + "_seen_once))"
                           for s in strategy_states])

        report_if_state_seen += "\n\t& " + \
                                "\n\t& ".join(["(((" + ("(turn == cs)") + " & " + s.split(" : ")[
                                    0] + " & " + s.split(" : ")[0] + "_seen_once "
                                               + ") " + " | " + s.split(" : ")[0] + "_seen_more_than_once) " +
                                               "<-> next(" + s.split(" : ")[0] + "_seen_more_than_once))"
                                               for s in strategy_states])

        text += "\t&" + report_if_state_seen + "\n"

    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text

def create_nuxmv_model(nuxmvModel):
    from warnings import warn
    warn('This method is deprecated.', DeprecationWarning, stacklevel=2)

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


def there_is_mismatch_between_program_and_strategy(system,
                                                   controller: bool,
                                                   mismatch_condition=None):
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
            there_is_no_mismatch, out = model_checker.invar_check(system, "compatible", None, config.mc)
        else:
            there_is_no_mismatch, out = model_checker.invar_check(system,
                                                                  "!(!compatible" + " & " + mismatch_condition + ")", None, config.mc)
            if there_is_no_mismatch:
                there_is_no_mismatch, out = model_checker.invar_check(system, "compatible", None, config.mc)

        return False, not there_is_no_mismatch, out
    else:
        return False, False, None
