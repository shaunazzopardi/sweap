from pysmt.shortcuts import Not, TRUE

from analysis.smt_checker import check
from programs.transition import Transition
from programs.util import safe_update_set_vals
from prop_lang.uniop import UniOp
from prop_lang.util import disjunct_formula_set, conjunct_formula_set, fnode_to_formula


def relevant_pred(transition, relevant_preds, predicate):
    # check if relevant for guard
    if any(True for v in predicate.variablesin() if v in transition.condition.variablesin()):
        return True
    # check if used in action (without identities)
    elif any(True for v in predicate.variablesin()
             if any(True for act in transition.action
                    if act.left != act.right
                       and (v == act.left or v in act.right.variablesin()))):
        return True
    elif any(True for v in predicate.variablesin() if any(True for p in relevant_preds if v in p.variablesin())):
        return True
    else:
        return False


def relevant_pred_g_u(guard, update, relevant_preds, predicate):
    # check if relevant for guard
    if any(True for v in predicate.variablesin() if v in guard.variablesin()):
        return True
    # check if used in action (without identities)
    elif any(True for v in predicate.variablesin()
             if any(True for act in update
                    if act.left != act.right
                       and (v == act.left or v in act.right.variablesin()))):
        return True
    elif any(True for v in predicate.variablesin() if any(True for p in relevant_preds if v in p.variablesin())):
        return True
    else:
        return False


def merge_transitions(transitions: [Transition], symbol_table, to_program_transitions):
    # can probably do this while building the initial abstraction
    new_transitions = []
    new_to_program_transitions = {}

    # partition the transitions into classes where in each class each transition has the same outputs and source and end state
    partitions = dict()
    for transition in transitions:
        key = str(transition.src) + str(
            conjunct_formula_set(sorted(transition.output, key=lambda x: str(x)))) + str(
            transition.tgt)
        if key in partitions.keys():
            partitions[key].append(transition)
        else:
            partitions[key] = [transition]
    if len(partitions) == len(transitions):
        return transitions, to_program_transitions
    for key in partitions.keys():
        trans_here = partitions[key]
        conditions = disjunct_formula_set(sorted([t.condition for t in trans_here], key=lambda x: str(x)))
        conditions_smt = conditions.to_smt(symbol_table)[0]
        # If negation is unsat
        if not check(Not(conditions_smt)):
            conditions_simplified_fnode = TRUE()
        else:
            conditions_simplified_fnode = conditions_smt  # simplify(conditions_smt)#.simplify()
        ## simplify when doing disjunct, after lex ordering
        ## also, may consider when enumerating possible event sets starting with missing some evetns and seeing how many transitions they match, if only then can stop adding to it
        try:
            new_tran = Transition(trans_here[0].src, fnode_to_formula(conditions_simplified_fnode), [],
                                  trans_here[0].output,
                                  trans_here[0].tgt)
            new_transitions.append(new_tran)

            if any(tt for tt in trans_here if tt not in to_program_transitions.keys()):
                raise Exception("Transition not in to program transitions")

            safe_update_set_vals(new_to_program_transitions, new_tran,
                                 set(t for tt in trans_here for t in to_program_transitions[tt]))
        except Exception as e:
            raise e
    return new_transitions, new_to_program_transitions

def tran_and_state_preds_after_con_env_step(env_trans: Transition):
    if True:
        src_tran_preds = [p for p in env_trans.src.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]
        tgt_tran_preds = [p for p in env_trans.tgt.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]

        pos = {p for p in (src_tran_preds + tgt_tran_preds) if not isinstance(p, UniOp)}
        all_neg = {p for p in (src_tran_preds + tgt_tran_preds) if isinstance(p, UniOp)}
        neg = {p for p in all_neg if p.right not in pos}

        state_preds = [p for p in env_trans.tgt.predicates
                       if [] == [v for v in p.variablesin() if v.name.endswith("_prev")]]

        return list(pos | neg) + state_preds
