from contextlib import contextmanager

from prop_lang.util import conjunct, neg


@contextmanager
def _push_sat_formula(sat_ctx, formula):
    sat_ctx._solver.push()
    sat_ctx._solver.add_assertion(sat_ctx._to_smt(formula))
    try:
        yield
    finally:
        sat_ctx._solver.pop()


def _refine_nexts_scoped(nexts, sat_ctx):
    new_nexts = []
    for next_formula in nexts:
        with _push_sat_formula(sat_ctx, next_formula):
            if sat_ctx._solver.solve():
                new_nexts.append(next_formula)
    return new_nexts


def _state_extend_effect_now_scoped(state_pred, old_effects, sat_ctx):
    new_effects = []
    if state_pred.is_bool or state_pred.is_input or "_prev" in str(state_pred.pred):
        return old_effects

    for now, nexts in old_effects:
        now_p = conjunct(now, state_pred.pred)
        with _push_sat_formula(sat_ctx, now_p.prev_rep()):
            now_p_sat = sat_ctx._solver.solve()
            if now_p_sat:
                new_nexts = _refine_nexts_scoped(nexts, sat_ctx)
                if len(new_nexts) == 0:
                    continue
                new_effects.append((now_p, new_nexts))

        if not now_p_sat:
            now_neg_p = conjunct(now, neg(state_pred.pred))
            with _push_sat_formula(sat_ctx, now_neg_p.prev_rep()):
                new_nexts = _refine_nexts_scoped(nexts, sat_ctx)
                if len(new_nexts) == 0:
                    continue
                new_effects.append((now_neg_p, new_nexts))
            continue

        now_neg_p = conjunct(now, neg(state_pred.pred))
        with _push_sat_formula(sat_ctx, now_neg_p.prev_rep()):
            if sat_ctx._solver.solve():
                new_nexts = _refine_nexts_scoped(nexts, sat_ctx)
                if len(new_nexts) == 0:
                    continue
                new_effects.append((now_neg_p, new_nexts))

    return new_effects


def _state_refine_nexts_with_pred_scoped(state_pred, nexts, sat_ctx):
    new_nexts = []
    for next_formula in nexts:
        next_p = conjunct(next_formula, state_pred.pred)
        with _push_sat_formula(sat_ctx, next_p):
            if sat_ctx._solver.solve():
                new_nexts.append(next_p)

        next_neg_p = conjunct(next_formula, neg(state_pred.pred))
        with _push_sat_formula(sat_ctx, next_neg_p):
            if sat_ctx._solver.solve():
                new_nexts.append(next_neg_p)
    return new_nexts


def _state_extend_effect_next_scoped(state_pred, old_effects, sat_ctx):
    if state_pred.is_bool or state_pred.is_input:
        return old_effects
    new_effects = []
    for now, nexts in old_effects:
        with _push_sat_formula(sat_ctx, now.prev_rep()):
            new_nexts = _state_refine_nexts_with_pred_scoped(state_pred, nexts, sat_ctx)
            if len(new_nexts) == 0:
                continue
            new_effects.append((now, new_nexts))
    return new_effects


def _state_extend_effect_scoped(state_pred, old_effects, sat_ctx):
    if state_pred.is_bool:
        return old_effects
    if state_pred.is_input:
        return _state_extend_effect_now_scoped(state_pred, old_effects, sat_ctx)

    new_effects = []
    for now, nexts in old_effects:
        now_p = conjunct(now, state_pred.pred)
        with _push_sat_formula(sat_ctx, now_p.prev_rep()):
            now_p_sat = sat_ctx._solver.solve()
            if now_p_sat:
                new_nexts = _state_refine_nexts_with_pred_scoped(
                    state_pred, nexts, sat_ctx
                )
                if len(new_nexts) > 0:
                    new_effects.append((now_p, new_nexts))

        if not now_p_sat:
            now_neg_p = conjunct(now, neg(state_pred.pred))
            with _push_sat_formula(sat_ctx, now_neg_p.prev_rep()):
                new_nexts = _state_refine_nexts_with_pred_scoped(
                    state_pred, nexts, sat_ctx
                )
                if len(new_nexts) > 0:
                    new_effects.append((now_neg_p, new_nexts))
            continue

        now_neg_p = conjunct(now, neg(state_pred.pred))
        with _push_sat_formula(sat_ctx, now_neg_p.prev_rep()):
            if sat_ctx._solver.solve():
                new_nexts = _state_refine_nexts_with_pred_scoped(
                    state_pred, nexts, sat_ctx
                )
                if len(new_nexts) > 0:
                    new_effects.append((now_neg_p, new_nexts))
    return new_effects


def _chain_expand_candidates(chain_pred, gu, old_formula, now_or_next):
    return chain_pred.replace_formulas_multiple_but(
        chain_pred.old_to_new, old_formula, gu, now_or_next
    )


def _chain_refine_nexts_scoped(chain_pred, gu, prev_state, nexts, sat_ctx):
    new_nexts = []
    for old_next in nexts:
        candidates = _chain_expand_candidates(chain_pred, gu, old_next, False)
        for next_formula in candidates:
            with _push_sat_formula(sat_ctx, next_formula):
                if sat_ctx._solver.solve():
                    new_nexts.append(next_formula)
    return new_nexts


def _chain_extend_effect_now_scoped(chain_pred, gu, old_effects, sat_ctx):
    new_effects = []
    for old_now, nexts in old_effects:
        new_nows = _chain_expand_candidates(chain_pred, gu, old_now, True)
        for new_now in new_nows:
            prev_state = conjunct(gu, new_now.prev_rep())
            with _push_sat_formula(sat_ctx, prev_state):
                if sat_ctx._solver.solve():
                    new_nexts = _refine_nexts_scoped(nexts, sat_ctx)
                    if len(new_nexts) > 0:
                        new_effects.append((new_now, new_nexts))
    return new_effects


def _chain_extend_effect_next_scoped(chain_pred, gu, old_effects, sat_ctx):
    if chain_pred.is_input:
        return old_effects

    new_effects = []
    for now, nexts in old_effects:
        prev_state = conjunct(gu, now.prev_rep())
        with _push_sat_formula(sat_ctx, prev_state):
            new_nexts = _chain_refine_nexts_scoped(
                chain_pred,
                gu,
                prev_state,
                nexts,
                sat_ctx,
            )
            if len(new_nexts) > 0:
                new_effects.append((now, new_nexts))
    return new_effects


def _chain_extend_effect_scoped(chain_pred, gu, old_effects, sat_ctx):
    if chain_pred.is_input:
        return _chain_extend_effect_now_scoped(chain_pred, gu, old_effects, sat_ctx)

    new_effects = []
    for old_now, nexts in old_effects:
        new_nows = _chain_expand_candidates(chain_pred, gu, old_now, True)
        for new_now in new_nows:
            prev_state = conjunct(gu, new_now.prev_rep())
            with _push_sat_formula(sat_ctx, prev_state):
                if sat_ctx._solver.solve():
                    new_nexts = _chain_refine_nexts_scoped(
                        chain_pred,
                        gu,
                        prev_state,
                        nexts,
                        sat_ctx,
                    )
                    if len(new_nexts) > 0:
                        new_effects.append((new_now, new_nexts))
    return new_effects
