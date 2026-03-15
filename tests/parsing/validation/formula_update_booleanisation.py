"""Validation-local helper for formula update booleanisation."""

from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.types.values import BoolAtoms
from prop_lang.util import X, atomic_predicates, neg, stringify_pred, strip_mathexpr
from prop_lang.variable import Variable


def extract_formula_updates(program, formula_objective):
    preds_to_replace = {}
    to_add_non_det_trans = set()
    new_con_props = set()

    preds = atomic_predicates(formula_objective)
    for pred in preds:
        pred = strip_mathexpr(pred)
        unk_next_vars_in_pred = [
            v
            for v in pred.variablesin()
            if v.is_next() and v.prev_rep().name not in program.symbol_table.keys()
        ]
        if len(unk_next_vars_in_pred) != 1:
            to_add_non_det_trans.update(unk_next_vars_in_pred)
            continue

        next_var = unk_next_vars_in_pred[0]
        if isinstance(pred, Variable):
            preds_to_replace[next_var] = X(next_var.prev_rep())
            new_con_props.add(next_var.prev_rep())
            continue

        if not isinstance(pred, BiOp):
            to_add_non_det_trans.update(unk_next_vars_in_pred)
            continue

        if pred.op == "!=":
            normalized_pred = BiOp(pred.left, "=", pred.right)
            preds_to_replace[pred] = neg(normalized_pred)
            pred = normalized_pred
        elif pred.op != "=":
            to_add_non_det_trans.update(unk_next_vars_in_pred)
            continue

        var = pred.left if isinstance(pred.left, Variable) else pred.right
        val = pred.right if var == pred.left else pred.left
        if isinstance(val.val, BoolAtoms):
            preds_to_replace[pred] = (
                X(var.prev_rep())
                if val.val == BoolAtoms.TRUE
                else neg(X(var.prev_rep()))
            )
            new_con_props.add(var.prev_rep())
        elif any(
            p1
            for p1 in preds
            for vv in unk_next_vars_in_pred
            if vv.prev_rep() in p1.variablesin()
        ):
            to_add_non_det_trans.update(unk_next_vars_in_pred)
        else:
            bool_var = Variable(stringify_pred(pred).name + "_bool")
            preds_to_replace[pred] = X(bool_var)
            preds_to_replace[MathExpr(pred)] = X(bool_var)
            new_con_props.add(bool_var.prev_rep())

    return preds_to_replace, to_add_non_det_trans, new_con_props

