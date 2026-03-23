import config
from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.smt_checker import choose_model
from programs.util import binary_rep
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    atomic_predicates,
    G,
    X,
    conjunct_formula_set,
    conjunct,
    disjunct_formula_set,
    implies,
    F,
    propagate_nexts,
    massage_ltl_for_dual,
    neg,
    iff,
    sat,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import (
    AbstractLTLSynthesisProblem,
)
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem


def to_ltl_organised_by_pred_effects_guard_updates(
    predicate_abstraction: EffectsAbstraction, env_lose, con_pred_props
):
    rename_pred = lambda x: x.replace_formulas(predicate_abstraction.var_relabellings)
    program = predicate_abstraction.program
    dualise = config.Config.getConfig().dual
    dual2 = config.Config.getConfig().dual2
    strix_backend = config.Config.getConfig().backend == "strix"

    init_explicit_state = program.states_binary_map[
        predicate_abstraction.program.initial_state
    ]

    if dualise:
        init_explicit_state = conjunct(init_explicit_state, X(init_explicit_state))
        if strix_backend:
            init_explicit_state = propagate_nexts(init_explicit_state)

    if (dualise or dual2) and len(predicate_abstraction.init_state_abstraction) > 1:
        raw_env_vars = [
            i for i in range(0, len(predicate_abstraction.init_state_abstraction))
        ]
        new_env_vars, bin_map = binary_rep(
            raw_env_vars,
            "env_init_",
            printing=False,
            log=False,
        )
        vars_to_reuse = (
            len(new_env_vars)
            if len(con_pred_props) >= len(new_env_vars)
            else len(con_pred_props)
        )
        reused_events = list(con_pred_props)
        to_replace = {}
        for i in range(vars_to_reuse):
            to_replace[new_env_vars[i]] = reused_events[i]
            new_env_vars[i] = reused_events[i]

        bin_map = {k: v.replace_formulas(to_replace) for k, v in bin_map.items()}

        init_preds = [
            (
                [bin_map[raw_env_vars[i]]]
                + [
                    (
                        (
                            X(rename_pred(p))
                            if not strix_backend
                            else propagate_nexts(X(rename_pred(p)))
                        )
                        if dualise  # else dual2
                        else rename_pred(p)
                    )
                    for p in f
                    if not (isinstance(p, Value) and p.is_true())
                    if not predicate_abstraction.has_input_vars(p)
                ]
            )
            for i, f in enumerate(predicate_abstraction.init_state_abstraction)
        ]

        init_preds = list(map(conjunct_formula_set, init_preds))
        init = (
            disjunct_formula_set(init_preds),
            new_env_vars,
        )
        if config.Config.getConfig().debug:
            f = disjunct_formula_set(
                [
                    bin_map[raw_env_vars[i]]
                    for i in range(0, len(predicate_abstraction.init_state_abstraction))
                ]
            )
            if sat(neg(f), {str(v): BOOLEAN for v in f.variablesin()}):
                model = choose_model(
                    neg(f).to_smt({str(v): BOOLEAN for v in f.variablesin()})[0]
                )
                print(model)
                raise Exception("Init abstraction is unsat!")
    else:
        init_preds = [
            conjunct_formula_set(
                [
                    (
                        rename_pred(p)
                        if not dualise
                        else (
                            X(rename_pred(p))
                            if not strix_backend
                            else propagate_nexts(X(rename_pred(p)))
                        )
                    )
                    for p in f
                    if not (isinstance(p, Value) and p.is_true())
                ]
            )
            for f in predicate_abstraction.init_state_abstraction
        ]
        init = (disjunct_formula_set(init_preds), [])
    print("No of init models: " + str(len(init_preds)))

    init_constants = [
        (
            rename_pred(p)
            if not dualise
            else (
                conjunct(rename_pred(p), X(rename_pred(p)))
                if not strix_backend
                else propagate_nexts(X(rename_pred(p)))
            )
        )
        for p in predicate_abstraction.init_constants
    ]

    transition_terms_by_src = {}
    for gu in predicate_abstraction.gu_to_trans.keys():
        tt = predicate_abstraction.gu_to_trans[gu][0]
        cond = tt.condition

        if dualise:
            cond: Formula = massage_ltl_for_dual(
                cond, [v for v, _ in predicate_abstraction.program.env_events], False
            )
        elif dual2:
            cond: Formula = massage_ltl_for_dual(
                cond,
                predicate_abstraction.program.bool_in_out
                + predicate_abstraction.program.num_in_out,
                False,
            )

        cond = cond.replace_formulas(predicate_abstraction.var_relabellings)
        if dualise:
            cond = X(cond)
            if strix_backend:
                cond = propagate_nexts(cond)
        # effects comes with X already applied, and propagated in case of using strix
        effect = predicate_abstraction.abstract_effect_ltl[gu]

        for t in predicate_abstraction.gu_to_trans[gu]:
            bin_src = program.states_binary_map[t.src]
            if dualise:
                if env_lose:
                    bin_src = X(
                        # conjunct(neg(F(env_lose)), bin_src)
                        conjunct(conjunct(neg(env_lose), X(neg(env_lose))), bin_src)
                    )
                else:
                    bin_src = X(bin_src)
                if strix_backend:
                    bin_src = propagate_nexts(bin_src)

            pred_effect_formula = effect
            if len(t.output) > 0:
                output_formula = conjunct_formula_set([X(o) for o in t.output])
                effect_formula = conjunct(pred_effect_formula, output_formula)
            else:
                effect_formula = pred_effect_formula

            bin_tgt = program.states_binary_map[t.tgt]
            if dualise:
                bin_tgt = X(bin_tgt)

            next = conjunct(
                effect_formula,
                X(bin_tgt) if not strix_backend else propagate_nexts(X(bin_tgt)),
            )

            if t in predicate_abstraction.non_init_program_trans:
                if bin_src not in transition_terms_by_src:
                    transition_terms_by_src[bin_src] = {}
                src_terms = transition_terms_by_src[bin_src]
                next_key = str(next)
                if next_key not in src_terms:
                    src_terms[next_key] = {
                        "next": next,
                        "conds": {},
                    }
                src_terms[next_key]["conds"][str(cond)] = cond

    transition_ltl = {}
    for bin_src, next_map in transition_terms_by_src.items():
        merged_terms = []
        for item in next_map.values():
            conds = list(item["conds"].values())
            merged_cond = conds[0] if len(conds) == 1 else disjunct_formula_set(conds)
            merged_terms.append(conjunct(merged_cond, item["next"]))
        transition_ltl[bin_src] = (
            merged_terms[0]
            if len(merged_terms) == 1
            else disjunct_formula_set(merged_terms)
        )

    _transition_ltl = [
        (
            G(
                implies(
                    g,
                    (transition_ltl[g]),
                )
            )
        )
        for g in transition_ltl.keys()
    ]

    abs = [
        conjunct_formula_set([init_explicit_state] + init_constants)
    ] + _transition_ltl

    return None, abs, init


def abstract_ltl_problem(
    original_LTL_problem: LTLSynthesisProblem,
    effects_abstraction: EffectsAbstraction,
):
    env_predicate_vars = set()
    con_predicate_vars = set()
    dualise = config.Config.getConfig().dual
    dual2 = config.Config.getConfig().dual2
    strix_backend = config.Config.getConfig().backend == "strix"

    relabellings = {}
    if dual2:
        for var, label in effects_abstraction.var_relabellings.items():
            if var not in effects_abstraction.input_preds:
                relabellings[var] = label
            else:
                relabellings[var] = X(label)
        for v in effects_abstraction.program.bool_in_out:
            relabellings[v] = X(v)
        for v, l in effects_abstraction.program.states_binary_map.items():
            relabellings[v] = l
    else:
        relabellings = effects_abstraction.var_relabellings

    models = effects_abstraction.sat_input_models
    env_lose = None
    model_f = None
    models_are_sane = None
    if len(models) > 0:
        if dualise:
            model_f, models_are_sane = massage_models_for_dual(
                models, effects_abstraction
            )
            if models_are_sane:
                env_lose = Variable("env_lose")
                effects_abstraction.symbol_table[str(env_lose)] = BOOLEAN
        else:
            model_f = G(
                disjunct_formula_set(
                    [(m.replace_formulas(relabellings)) for m in models]
                )
            )

    # ltl_abstraction = to_ltl_reduced(effects_abstraction)
    for p in effects_abstraction.state_predicates:
        if dualise:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                con_predicate_vars.add(p.bool_var)
            else:
                env_predicate_vars.add(p.bool_var)
        elif dual2:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                env_predicate_vars.add(p.bool_var)
            else:
                con_predicate_vars.add(p.bool_var)
        else:
            env_predicate_vars.add(p.bool_var)

    for p in effects_abstraction.transition_predicates:
        if dual2:
            con_predicate_vars.update(p.bool_rep.values())
        else:
            env_predicate_vars.update(p.bool_rep.values())

    for _, p in effects_abstraction.v_to_chain_pred.items():
        if dualise:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                con_predicate_vars.update(p.bin_vars)
            else:
                env_predicate_vars.update(p.bin_vars)
        elif dual2:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                env_predicate_vars.update(p.bin_vars)
            else:
                con_predicate_vars.update(p.bin_vars)
        else:
            env_predicate_vars.update(p.bin_vars)

    program = effects_abstraction.get_program()
    env_pred_props = list(env_predicate_vars)
    con_pred_props = con_predicate_vars

    if dual2:
        con_pred_props.update(program.bin_state_vars)
    else:
        env_pred_props.extend(program.bin_state_vars)

    dict_to_replace = dict(program.states_binary_map)
    dict_to_replace |= effects_abstraction.var_relabellings

    loop_constraints = []
    # TODO need to get rankings from chain preds
    for (
        modif,
        ltl_constraints,
    ) in effects_abstraction.ranking_constraints.items():
        f = implies(G(F(modif)), propagate_nexts(conjunct_formula_set(ltl_constraints)))
        f = f.replace_formulas(dict_to_replace)
        loop_constraints.append(f)
        all_preds = set()
        all_preds |= atomic_predicates(f)
    for chain_pred in effects_abstraction.v_to_chain_pred.values():
        top_ranking = chain_pred.top_ranking
        if not top_ranking is None:
            loop_constraints.append(top_ranking.replace_formulas(dict_to_replace))
        bottom_ranking = chain_pred.bottom_ranking
        if not bottom_ranking is None:
            loop_constraints.append(bottom_ranking.replace_formulas(dict_to_replace))

    for f in effects_abstraction.structural_loop_constraints:
        f = f.replace_formulas(dict_to_replace | relabellings)
        if dualise or dual2:
            f = X(f)
        if strix_backend:
            f = propagate_nexts(f)
        loop_constraints.append(f)

    for p in effects_abstraction.loop_vars:
        if dualise:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                con_predicate_vars.add(p)
            else:
                env_predicate_vars.add(p)
        elif dual2:
            if any(
                v
                for v in p.variablesin()
                if v in effects_abstraction.program.num_in_out
            ):
                env_predicate_vars.add(p)
            else:
                con_predicate_vars.add(p)
        else:
            env_predicate_vars.add(p)

    orig_assumptions = []
    for ass in original_LTL_problem.assumptions:
        new_ass = ass.replace_formulas(dict_to_replace | relabellings)
        orig_assumptions.append(
            new_ass
            if not dualise
            else X(new_ass) if not strix_backend else propagate_nexts(X(new_ass))
        )

    orig_guarantees = []
    for guar in original_LTL_problem.guarantees:
        new_guar = guar.replace_formulas(dict_to_replace | relabellings)
        orig_guarantees.append(
            new_guar
            if not dualise
            else X(new_guar) if not strix_backend else propagate_nexts(X(new_guar))
        )

    env_pred_props = set(env_pred_props) | env_predicate_vars
    con_pred_props = con_pred_props | con_predicate_vars

    env_props = []
    con_props = []
    for v in original_LTL_problem.env_props:
        env_props.append(v)
    for v in original_LTL_problem.con_props:
        con_props.append(v)

    _, ltl_abstraction, init_preds = to_ltl_organised_by_pred_effects_guard_updates(
        effects_abstraction, env_lose, con_pred_props
    )

    assumptions = (
        loop_constraints + ltl_abstraction + orig_assumptions + [init_preds[0]]
    )
    guarantees = orig_guarantees

    if dual2:
        assumptions = []
        guarantees = (
            [init_preds[0]]
            + loop_constraints
            + ltl_abstraction
            + [
                implies(
                    conjunct_formula_set(orig_assumptions),
                    conjunct_formula_set(orig_guarantees),
                )
            ]
        )

    if model_f:
        if dualise:
            env_props.append(env_lose)
            assumptions += [
                neg(env_lose),
                neg(X(env_lose)),
                (
                    X(G(iff(neg(X(env_lose)), models_are_sane)))
                    if not strix_backend
                    else propagate_nexts(X(G(iff(neg(X(env_lose)), models_are_sane))))
                ),
            ]
            guarantees += [G(neg(env_lose))]
        elif dual2:
            assumptions.append(model_f)
        else:
            assumptions += [model_f]

    ltl_synthesis_problem = AbstractLTLSynthesisProblem(
        env_props,
        program.out_events,
        list(env_pred_props),
        list(set(con_props + list(con_pred_props) + init_preds[1])),
        assumptions,
        guarantees,
        init_preds[0] if dualise or dual2 else None,
    )

    return ltl_synthesis_problem


def massage_models_for_dual(models, abstraction):
    strix_backend = config.Config.getConfig().backend == "strix"
    var_rel = abstraction.var_relabellings

    sane_model = disjunct_formula_set(
        [
            conjunct_formula_set(
                [
                    p.replace_formulas(abstraction.var_relabellings)
                    for p in (
                        [m]
                        if not isinstance(m, BiOp)
                        else m.sub_formulas_up_to_associativity()
                    )
                ]
            )
            for m in abstraction.sat_input_models
        ]
    )

    new_models = [
        conjunct_formula_set(
            [
                (
                    X(p).replace_formulas(var_rel)
                    if not strix_backend
                    else propagate_nexts(X(p).replace_formulas(var_rel))
                )
                for p in (
                    m.sub_formulas_up_to_associativity() if isinstance(m, BiOp) else [m]
                )
            ]
        )
        for m in models
    ]

    return G(disjunct_formula_set(new_models)), sane_model
