from __future__ import annotations

from collections import defaultdict
from typing import TYPE_CHECKING

import config
from analysis.smt_checker import quantifier_elimination
from pysmt.shortcuts import Exists, ForAll, Symbol
from pysmt.typing import BOOL, INT
from programs.dfa import classify_initial_values
from programs.transition import Transition
from programs.util import binary_rep, reset_caches
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER, Type
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import (
    atomic_predicates,
    conjunct,
    conjunct_formula_set,
    fnode_to_formula,
    implies,
    is_tautology,
    neg,
    propagate_nexts,
    put_next_vars_on_left_side,
    reset_caches as prop_lang_util_reset_caches,
    sat,
    strip_mathexpr,
    true,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

if TYPE_CHECKING:
    from programs.program import Program
    from prop_lang.formula import Formula


class MinigameFiller:
    def __init__(
        self,
        program: Program,
        ltl_formulas: list[Formula],
        to_exclude_from_minigame,
        *,
        optimisation_counters: dict[str, int] | None = None,
    ):
        self.program = program
        self.ltl_formulas = ltl_formulas
        self.to_exclude_from_minigame = {str(x) for x in to_exclude_from_minigame}
        self.optimisation_counters = optimisation_counters

        self.symbol_table = program.symbol_table
        self.new_con_events: set[tuple[Variable, Type]] = set()
        self.bool_var_to_controller_prop: dict[str, Variable] = {}
        self.fresh_bool_prop_counter = 0
        self.ltl_forbidden_controller_names: set[str] = set()

    def _bump_optimisation_counter(self, kind: str, count: int = 1):
        if self.optimisation_counters is None or count <= 0:
            return
        self.optimisation_counters[kind] = (
            self.optimisation_counters.get(kind, 0) + count
        )

    @staticmethod
    def _collect_ltl_vars(formulas: list[Formula]):
        vars_used = set()
        for ltl in formulas:
            atoms = atomic_predicates(ltl)
            for p in atoms:
                for v in p.variablesin():
                    if v.is_next():
                        vars_used.add(v.prev_rep())
                    else:
                        vars_used.add(Variable(v.name.replace("_prev", "")))
        return vars_used

    @staticmethod
    def _local_init_values(prog: Program):
        init_values = []
        for var in sorted(prog.local_vars, key=lambda v: v.name):
            var_name = var.name
            var_type = prog.symbol_table[var_name]
            if var_name in prog.init_var_values:
                init_values.append((var_name, var_type, prog.init_var_values[var_name]))
            else:
                init_values.append((var_name, var_type))
        return init_values

    @staticmethod
    def _assert_no_conflicting_transitions(
        transitions: list[Transition],
        sym_table,
        mg_states: set[Variable],
        con_events: set[tuple[Variable, Type]],
    ):
        if not config.Config.getConfig().debug:
            return
        for t in transitions:
            for tt in transitions:
                if t == tt or t.src != tt.src:
                    continue
                if sat(
                    conjunct(t.condition, tt.condition),
                    sym_table
                    | {str(v): BOOLEAN for v in mg_states | {v[0] for v in con_events}},
                ):
                    raise Exception(
                        "Conflict in minigame transitions between \n"
                        + str(t)
                        + "\nand\n"
                        + str(tt)
                    )

    @staticmethod
    def _value_as_int(val: Formula):
        if not isinstance(val, Value):
            return None
        if isinstance(val.val, BoolAtoms):
            return None
        try:
            return int(str(val.val))
        except Exception:
            return None

    @staticmethod
    def _reverse_rel(op: str):
        return {
            "<": ">",
            "<=": ">=",
            ">": "<",
            ">=": "<=",
            "=": "=",
            "==": "==",
            "!=": "!=",
        }.get(op, op)

    def _extract_var_const_rel(self, atom: Formula):
        atom = strip_mathexpr(atom)
        if isinstance(atom, UniOp) and atom.op == "!":
            rel = self._extract_var_const_rel(atom.right)
            if rel is None:
                return None
            v, op, c = rel
            neg_rel = {
                "=": "!=",
                "==": "!=",
                "!=": "=",
                "<": ">=",
                "<=": ">",
                ">": "<=",
                ">=": "<",
            }.get(op)
            if neg_rel is None:
                return None
            return v, neg_rel, c
        if not isinstance(atom, BiOp):
            return None
        op = str(atom.op)
        left = atom.left
        right = atom.right
        if isinstance(left, Variable) and isinstance(right, Value):
            v = self._value_as_int(right)
            if v is None:
                return None
            return left, op, v
        if isinstance(right, Variable) and isinstance(left, Value):
            v = self._value_as_int(left)
            if v is None:
                return None
            return right, self._reverse_rel(op), v
        return None

    @staticmethod
    def _event_const_label(c: int):
        return ("m" + str(abs(c))) if c < 0 else str(c)

    @staticmethod
    def _pick_other_constant(constants: set[int]):
        if 0 not in constants:
            return 0
        if -1 not in constants:
            return -1
        c = max(constants) + 1
        while c in constants:
            c += 1
        return c

    def _collect_ltl_constant_comparison_profile(self):
        tracked_int_vars = {
            str(v)
            for v in self.program.local_vars
            if str(v) in self.symbol_table and self.symbol_table[str(v)] != BOOLEAN
        }
        only_const_cmp = {v: True for v in tracked_int_vars}
        cmp_consts = defaultdict(set)

        for ltl in self.ltl_formulas:
            for atom in atomic_predicates(ltl):
                atom = strip_mathexpr(atom)
                vars_in_atom = {
                    str(v).replace("'", "")
                    for v in atom.variablesin()
                    if str(v).replace("'", "") in tracked_int_vars
                }
                if len(vars_in_atom) == 0:
                    continue
                rel = self._extract_var_const_rel(atom)
                if rel is None:
                    for vn in vars_in_atom:
                        only_const_cmp[vn] = False
                    continue
                rel_var, rel_op, rel_val = rel
                rel_name = str(rel_var).replace("'", "")
                if (
                    rel_name in vars_in_atom
                    and len(vars_in_atom) == 1
                    and rel_op in {"=", "==", "!="}
                ):
                    cmp_consts[rel_name].add(rel_val)
                else:
                    for vn in vars_in_atom:
                        only_const_cmp[vn] = False
        return only_const_cmp, cmp_consts

    def _collect_constant_update_profile(self):
        tracked_int_vars = {
            str(v)
            for v in self.program.local_vars
            if str(v) in self.symbol_table and self.symbol_table[str(v)] != BOOLEAN
        }
        only_const_updates = {v: True for v in tracked_int_vars}
        update_consts = defaultdict(set)

        for tr in self.program.transitions:
            for act in tr.action:
                v_name = str(act.left)
                if v_name not in tracked_int_vars:
                    continue
                if isinstance(act.right, NonDeterministic):
                    continue
                if isinstance(act.right, Variable) and act.right == act.left:
                    continue
                c = self._value_as_int(act.right)
                if c is None:
                    only_const_updates[v_name] = False
                else:
                    update_consts[v_name].add(c)

            for pred in tr.pred_upgrades:
                pred = strip_mathexpr(pred)
                next_vars = {
                    str(v.prev_rep())
                    for v in pred.variablesin()
                    if v.is_next() and str(v.prev_rep()) in tracked_int_vars
                }
                if len(next_vars) == 0:
                    continue
                rel = self._extract_var_const_rel(pred)
                if rel is None:
                    for vn in next_vars:
                        only_const_updates[vn] = False
                    continue
                rel_var, rel_op, rel_val = rel
                rel_name = (
                    str(rel_var.prev_rep()) if rel_var.is_next() else str(rel_var)
                )
                if (
                    rel_name in next_vars
                    and len(next_vars) == 1
                    and rel_op in {"=", "==", "!="}
                ):
                    update_consts[rel_name].add(rel_val)
                else:
                    for vn in next_vars:
                        only_const_updates[vn] = False
        return only_const_updates, update_consts

    @staticmethod
    def _actions_as_next_equalities(actions: list[Update]) -> list[Formula]:
        eqs = []
        for act in actions:
            if isinstance(act.right, NonDeterministic):
                continue
            eqs.append(BiOp(Variable(str(act.left) + "'"), "=", act.right))
        return eqs

    def _antecedent_implies(self, antecedent: Formula, consequent: Formula) -> bool:
        return is_tautology(implies(antecedent, consequent), self.symbol_table)

    @staticmethod
    def _strip_prev_suffix(name: str) -> str:
        while True:
            if name.endswith("_prev_prev"):
                name = name[: -len("_prev_prev")]
                continue
            if name.endswith("_prev"):
                name = name[: -len("_prev")]
                continue
            return name

    def _is_program_input_var(self, v: Variable) -> bool:
        return any(v == inp for inp in self.program.inputs)

    @classmethod
    def _formula_base_var_names(cls, formula: Formula) -> set[str]:
        names = set()
        for var in formula.variablesin():
            base = var.prev_rep() if var.is_next() else var
            names.add(cls._strip_prev_suffix(str(base)))
        return names

    @classmethod
    def _collect_ltl_unprimed_related_to_primed_names(
        cls, formulas: list[Formula]
    ) -> set[str]:
        rel_ops = {"=", "!=", "<", "<=", ">", ">="}

        def _collect_term_vars_with_context(
            term: Formula, next_depth: int
        ) -> tuple[set[str], set[str]]:
            t = strip_mathexpr(term)
            if isinstance(t, Value):
                return set(), set()
            if isinstance(t, Variable):
                base_name = cls._strip_prev_suffix(
                    str(t.prev_rep()) if t.is_next() else str(t)
                )
                if t.is_next() or next_depth > 0:
                    return set(), {base_name}
                return {base_name}, set()
            if isinstance(t, UniOp):
                if t.op == "X":
                    return _collect_term_vars_with_context(t.right, next_depth + 1)
                return _collect_term_vars_with_context(t.right, next_depth)
            if isinstance(t, BiOp):
                left_unprimed, left_primed = _collect_term_vars_with_context(
                    t.left, next_depth
                )
                right_unprimed, right_primed = _collect_term_vars_with_context(
                    t.right, next_depth
                )
                return (left_unprimed | right_unprimed, left_primed | right_primed)
            return set(), set()

        def _walk_formula(f: Formula, next_depth: int, out: set[str]):
            q = strip_mathexpr(f)
            if isinstance(q, UniOp):
                if q.op == "X":
                    _walk_formula(q.right, next_depth + 1, out)
                else:
                    _walk_formula(q.right, next_depth, out)
                return
            if isinstance(q, BiOp):
                if str(q.op) in rel_ops:
                    left_unprimed, left_primed = _collect_term_vars_with_context(
                        q.left, next_depth
                    )
                    right_unprimed, right_primed = _collect_term_vars_with_context(
                        q.right, next_depth
                    )
                    if len(left_primed | right_primed) > 0:
                        out.update(left_unprimed | right_unprimed)
                else:
                    _walk_formula(q.left, next_depth, out)
                    _walk_formula(q.right, next_depth, out)

        names = set()
        for ltl in formulas:
            propagated_ltl = propagate_nexts(strip_mathexpr(ltl))
            _walk_formula(propagated_ltl, 0, names)
        return names

    def _fresh_bool_controller_prop(self) -> Variable:
        while True:
            name = f"minigame_bool_event_{self.fresh_bool_prop_counter}"
            self.fresh_bool_prop_counter += 1
            if name not in self.symbol_table:
                return Variable(name)

    def _determinise_bool_nondet_updates(
        self, transition: Transition, nondet_updates: list[Update]
    ):
        bool_nondet_updates = [
            u for u in nondet_updates if self.symbol_table[str(u.left)] == BOOLEAN
        ]
        if len(bool_nondet_updates) == 0:
            return [], nondet_updates, {}

        remaining_nondet_updates = [
            u for u in nondet_updates if self.symbol_table[str(u.left)] != BOOLEAN
        ]
        forbidden_props = self._formula_base_var_names(transition.condition).union(
            self.ltl_forbidden_controller_names
        )
        available_props = sorted(
            {
                var
                for var, var_type in (
                    set(self.program.con_events) | self.new_con_events
                )
                if var_type == BOOLEAN and str(var) not in forbidden_props
            },
            key=lambda v: str(v),
        )

        chosen_props: dict[str, Variable] = {}
        used_in_transition = set()
        for upd in bool_nondet_updates:
            var_name = str(upd.left)
            mapped_prop = self.bool_var_to_controller_prop.get(var_name)
            if (
                mapped_prop is not None
                and str(mapped_prop) not in forbidden_props
                and mapped_prop not in used_in_transition
            ):
                chosen_props[var_name] = mapped_prop
                used_in_transition.add(mapped_prop)

        deterministic_updates = []
        next_var_replacements = {}
        for upd in bool_nondet_updates:
            var = upd.left
            var_name = str(var)
            prop = chosen_props.get(var_name)
            if prop is None:
                for candidate in available_props:
                    if candidate in used_in_transition:
                        continue
                    prop = candidate
                    break
            if prop is None:
                prop = self._fresh_bool_controller_prop()
                self.symbol_table[str(prop)] = BOOLEAN
                self.new_con_events.add((prop, BOOLEAN))
                available_props.append(prop)

            chosen_props[var_name] = prop
            used_in_transition.add(prop)
            self.bool_var_to_controller_prop[var_name] = prop
            deterministic_updates.append(Update(var, prop))
            next_var_replacements[Variable(var.name + "'")] = prop

        return deterministic_updates, remaining_nondet_updates, next_var_replacements

    @staticmethod
    def normalise_mg_preds(mg_preds: list[Formula]):
        normalised = []
        of_other_forms = []
        for p in mg_preds:
            p = strip_mathexpr(p)
            try:
                _, norm = put_next_vars_on_left_side(p)
                normalised.append(norm)
            except Exception:
                of_other_forms.append(p)

        mg_dict: dict[Variable, list[Formula]] = {}
        if len(of_other_forms) > 0:
            print("of other forms:", ", ".join(map(str, of_other_forms)))

        for p in normalised + of_other_forms:
            next_vars = frozenset(v for v in p.variablesin() if v.is_next())
            for v in next_vars:
                v_prev = v.prev_rep()
                if v_prev in mg_dict:
                    mg_dict[v_prev].append(p)
                else:
                    mg_dict[v_prev] = [p]
        return normalised + of_other_forms, mg_dict

    def _collect_run_profiles(self):
        vars_in_ltl = self._collect_ltl_vars(self.ltl_formulas)
        ltl_only_const_cmp, ltl_cmp_consts = (
            self._collect_ltl_constant_comparison_profile()
        )
        only_const_updates, update_consts = self._collect_constant_update_profile()
        ltl_unprimed_related_to_primed_names = (
            self._collect_ltl_unprimed_related_to_primed_names(self.ltl_formulas)
        )
        self.ltl_forbidden_controller_names = {
            self._strip_prev_suffix(str(v)) for v in vars_in_ltl
        }
        return (
            vars_in_ltl,
            ltl_only_const_cmp,
            ltl_cmp_consts,
            only_const_updates,
            update_consts,
            ltl_unprimed_related_to_primed_names,
        )

    @staticmethod
    def _make_normalise_losing(to_exclude_from_minigame):
        return lambda x: "lose" if str(x) in to_exclude_from_minigame else str(x)

    def _finalise_no_minigame_program(
        self,
        *,
        new_trans,
        minigame_states,
        normalise_losing,
        extra_local_init_values=None,
    ):
        from programs.program import Program

        reset_caches()
        prop_lang_util_reset_caches()
        self._assert_no_conflicting_transitions(
            new_trans, self.symbol_table, minigame_states, self.new_con_events
        )
        normalised_states = set(map(normalise_losing, self.program.states))
        if any(str(tr.src) == "lose" or str(tr.tgt) == "lose" for tr in new_trans):
            normalised_states.add("lose")
        if extra_local_init_values is None:
            extra_local_init_values = set()

        new_prog = Program(
            name=self.program.name,
            sts=list(normalised_states),
            init_st=normalise_losing(self.program.initial_state),
            init_values=list(
                set(self._local_init_values(self.program))
                | set(extra_local_init_values)
            ),
            transitions=new_trans,
            env_events=self.program.env_events,
            con_events=list(set(self.program.con_events) | self.new_con_events),
            preprocess=False,
            emit_state_binary_map=False,
        )
        return new_prog, []

    def _finalise_with_minigames_program(
        self,
        *,
        new_trans,
        minigame_states,
        new_states,
        new_init_var_values,
        extra_local_init_values=None,
        normalise_losing,
    ):
        from programs.program import Program

        reset_caches()
        prop_lang_util_reset_caches()
        if extra_local_init_values is None:
            extra_local_init_values = set()
        normalised_states = set(
            map(normalise_losing, self.program.states | set(new_states))
        )
        if any(str(tr.src) == "lose" or str(tr.tgt) == "lose" for tr in new_trans):
            normalised_states.add("lose")
        new_prog = Program(
            name=self.program.name,
            sts=list(normalised_states),
            init_st=normalise_losing(self.program.initial_state),
            init_values=list(
                set(self._local_init_values(self.program))
                | new_init_var_values
                | set(extra_local_init_values)
            ),
            transitions=set(new_trans),
            env_events=self.program.env_events,
            con_events=list(set(self.program.con_events) | self.new_con_events),
            preprocess=False,
            emit_state_binary_map=False,
        )
        return new_prog, list(minigame_states)

    def run(self):
        (
            vars_in_ltl,
            ltl_only_const_cmp,
            ltl_cmp_consts,
            only_const_updates,
            update_consts,
            ltl_unprimed_related_to_primed_names,
        ) = self._collect_run_profiles()

        no_mini_games_added = True
        to_add_to_local_vars = set()
        curr_state_init_values = set()
        bool_updates = set()
        minigame_states = set()
        new_states = []
        new_trans = []
        var_values_that_matter_from_state = {}
        mini_game_counter = 0
        existing_mini_games_from_with: dict[
            str, dict[tuple[frozenset[Variable], Formula], str]
        ] = {}
        to_exclude_from_minigame = list(map(str, self.to_exclude_from_minigame))
        lose_self_loop = None
        if len(to_exclude_from_minigame) > 0:
            lose_self_loop = Transition("lose", true(), [], [], "lose")
            new_trans.append(lose_self_loop)

        normalise_losing = self._make_normalise_losing(to_exclude_from_minigame)

        for t in self.program.transitions:
            if t.src in to_exclude_from_minigame:
                continue

            if t.tgt in to_exclude_from_minigame:
                new_t = Transition(t.src, t.condition, [], [], "lose")
                new_trans.append(new_t)
                continue

            non_determined_updates = [
                a for a in t.action if isinstance(a.right, NonDeterministic)
            ]
            if len(non_determined_updates) == 0:
                t.pred_upgrades = []
                new_trans.append(t)
                continue

            if t.tgt in var_values_that_matter_from_state:
                relevant = var_values_that_matter_from_state[t.tgt]
            else:
                relevant, _ = classify_initial_values(self.program, t.tgt)
                relevant.update(vars_in_ltl)

            new_non_determined_updates = []
            for u in non_determined_updates:
                if u.left in relevant:
                    new_non_determined_updates.append(u)
                else:
                    relevant_preds = [
                        p
                        for p in t.pred_upgrades
                        if u.left in p.prev_rep().variablesin()
                    ]
                    if relevant_preds:
                        now_vars = set(
                            Symbol(str(v), INT)
                            for p in relevant_preds
                            for v in p.variablesin()
                            if not v.is_next()
                        )
                        now_vars.update(
                            {
                                Symbol(
                                    str(v),
                                    (
                                        BOOL
                                        if self.symbol_table[str(v)] == BOOLEAN
                                        else INT
                                    ),
                                )
                                for v in t.condition.variablesin()
                            }
                        )
                        next_vars = set(
                            Symbol(str(v), INT)
                            for p in relevant_preds
                            for v in p.variablesin()
                            if v.is_next()
                        )
                        qe_formula = conjunct_formula_set(
                            [t.condition] + list(t.pred_upgrades)
                        ).to_smt(self.symbol_table)[0]
                        qe_formula = ForAll(now_vars, Exists(next_vars, qe_formula))
                        result = quantifier_elimination(qe_formula)
                        result = fnode_to_formula(result)
                        if not is_tautology(result, self.symbol_table):
                            new_non_determined_updates.append(u)

            effective_non_determined_updates = new_non_determined_updates
            base_actions = [
                a for a in t.action if not isinstance(a.right, NonDeterministic)
            ]
            (
                bool_formula_updates,
                effective_non_determined_updates,
                bool_next_replacements,
            ) = self._determinise_bool_nondet_updates(
                t, effective_non_determined_updates
            )
            if len(bool_formula_updates) > 0:
                base_actions = base_actions + bool_formula_updates
            if len(bool_next_replacements) > 0:
                t.set_predicate_upgrades(
                    [
                        p.replace_formulas(bool_next_replacements)
                        for p in t.pred_upgrades
                    ]
                )
            if len(effective_non_determined_updates) == 0:
                new_t = Transition(t.src, t.condition, base_actions, [], t.tgt)
                new_trans.append(new_t)
                continue

            non_determined_updates = effective_non_determined_updates
            t.action = base_actions + non_determined_updates
            var_values_that_matter_from_state[t.tgt] = relevant

            undetermined_vars: frozenset[Variable] = frozenset(
                u.left for u in non_determined_updates
            )
            mg_preds_key = conjunct_formula_set(p.prev_rep() for p in t.pred_upgrades)
            minigame_params = (undetermined_vars, mg_preds_key)
            if (
                t.tgt in existing_mini_games_from_with
                and minigame_params in existing_mini_games_from_with[t.tgt]
            ):
                start_state = existing_mini_games_from_with[t.tgt][minigame_params]
                new_t = Transition(
                    t.src,
                    t.condition,
                    [a for a in t.action if a not in non_determined_updates],
                    [],
                    start_state,
                )
                reuse_input_dependent = sorted(
                    {
                        v
                        for p in t.pred_upgrades
                        for v in p.variablesin()
                        if self._is_program_input_var(v)
                        and len([vv for vv in p.variablesin() if vv.is_next()]) > 0
                    },
                    key=str,
                )
                if len(reuse_input_dependent) > 0:
                    existing_lefts = {str(a.left) for a in new_t.action}
                    for inp in reuse_input_dependent:
                        curr_inp = Variable("curr_" + inp.name)
                        if str(curr_inp) not in self.symbol_table:
                            self.symbol_table[str(curr_inp)] = self.symbol_table[
                                str(inp)
                            ]
                            curr_state_init_values.add(
                                (str(curr_inp), self.symbol_table[str(inp)])
                            )
                        if str(curr_inp) not in existing_lefts:
                            new_t.action.append(Update(curr_inp, inp))
                new_trans.append(new_t)
                continue

            start_state = t.tgt + "_minigame_" + str(mini_game_counter)
            minigame_states.add(Variable(start_state))
            new_states.append(start_state)
            end_state = t.tgt
            new_t = Transition(
                t.src,
                t.condition,
                [a for a in t.action if a not in non_determined_updates],
                [],
                start_state,
            )
            mg_preds = t.pred_upgrades
            nondet_next_vars = {
                Variable(u.left.name + "'") for u in non_determined_updates
            }

            # Discharge deterministic next-vars before minigame stop predicate
            # construction. These vars are fixed by the entry/base actions and
            # must not survive as primed literals in generated guards.
            deterministic_next_subs = {
                Variable(a.left.name + "'"): a.right
                for a in base_actions
                if not isinstance(a.right, NonDeterministic)
            }
            if len(deterministic_next_subs) > 0:
                reduced_mg_preds = []
                for p in mg_preds:
                    pp = p.replace_formulas(deterministic_next_subs).simplify()
                    if isinstance(pp, Value) and pp.is_true():
                        continue
                    reduced_mg_preds.append(pp)
                mg_preds = reduced_mg_preds

            inputs_updates_depend_on = sorted(
                {
                    v
                    for p in mg_preds
                    for v in p.variablesin()
                    if self._is_program_input_var(v)
                    and len([vv for vv in p.variablesin() if vv.is_next()]) > 0
                },
                key=str,
            )
            input_snapshot_replacements = {}
            input_snapshot_updates = []
            for inp in inputs_updates_depend_on:
                curr_inp = Variable("curr_" + inp.name)
                input_snapshot_replacements[inp] = curr_inp
                if str(curr_inp) not in self.symbol_table:
                    self.symbol_table[str(curr_inp)] = self.symbol_table[str(inp)]
                    curr_state_init_values.add(
                        (str(curr_inp), self.symbol_table[str(inp)])
                    )
                input_snapshot_updates.append(Update(curr_inp, inp))
            if len(input_snapshot_replacements) > 0:
                mg_preds = [
                    p.replace_formulas(input_snapshot_replacements) for p in mg_preds
                ]
                existing_lefts = {str(a.left) for a in new_t.action}
                new_t.action.extend(
                    u
                    for u in input_snapshot_updates
                    if str(u.left) not in existing_lefts
                )

            mg_preds_key = conjunct_formula_set(mg_preds)
            undet_vars = []

            def upd_type(v, op, right):
                if op in {"="}:
                    return Update(v, right), None
                if op == "!=":
                    return None
                if op == "<":
                    return Update(v, BiOp(right, "-", Value(1))), "dec"
                if op == ">":
                    return Update(v, BiOp(right, "+", Value(1))), "inc"
                if op == "<=":
                    return Update(v, right), "dec"
                if op == ">=":
                    return Update(v, right), "inc"
                raise Exception("Unsupported operator in predicate: " + str(op))

            to_replace_preds = {}
            restricted_updates = []
            unrestricted_updates = []
            _, v_to_pred = self.normalise_mg_preds(mg_preds)

            def _collect_local_next_consts(v: Variable):
                local_consts = set()
                for pred in v_to_pred.get(v, []):
                    pred = strip_mathexpr(pred)
                    next_vars = {
                        str(vv.prev_rep()) for vv in pred.variablesin() if vv.is_next()
                    }
                    if str(v) not in next_vars:
                        continue
                    rel = self._extract_var_const_rel(pred)
                    if rel is None:
                        return False, set()
                    rel_var, rel_op, rel_val = rel
                    rel_name = (
                        str(rel_var.prev_rep()) if rel_var.is_next() else str(rel_var)
                    )
                    if (
                        rel_name == str(v)
                        and len(next_vars) == 1
                        and rel_op in {"=", "==", "!="}
                    ):
                        local_consts.add(rel_val)
                    else:
                        return False, set()
                return True, local_consts

            one_step_const_candidates = {}
            for u in non_determined_updates:
                v = u.left
                if (
                    not self.symbol_table[str(v)] == BOOLEAN
                    and v in v_to_pred
                    and len(v_to_pred[v]) == 1
                    and v_to_pred[v][0].left.prev_rep() == v
                ):
                    update_type = upd_type(v, v_to_pred[v][0].op, v_to_pred[v][0].right)
                    if update_type:
                        restricted_updates.append(update_type)
                        continue

                if self.symbol_table[str(u.left)] == BOOLEAN:
                    bool_updates.add(v)
                    unrestricted_updates.append(u)
                    continue

                unrestricted_updates.append(u)
                local_ok, local_consts = _collect_local_next_consts(v)
                candidate_consts = set(ltl_cmp_consts.get(str(v), set()))
                candidate_consts.update(update_consts.get(str(v), set()))
                candidate_consts.update(local_consts)
                if (
                    local_ok
                    and only_const_updates.get(str(v), False)
                    and ltl_only_const_cmp.get(str(v), False)
                    and len(candidate_consts) > 0
                ):
                    one_step_const_candidates[v] = candidate_consts

            one_step_const_var = None
            one_step_consts = []
            if len(restricted_updates) == 0 and len(unrestricted_updates) == 1:
                candidate_v = unrestricted_updates[0].left
                if (
                    candidate_v in one_step_const_candidates
                    and candidate_v not in bool_updates
                ):
                    one_step_const_var = candidate_v
                    one_step_consts = sorted(one_step_const_candidates[candidate_v])

            const_choice_updates = {
                u.left: sorted(one_step_const_candidates[u.left])
                for u in unrestricted_updates
                if u.left in one_step_const_candidates and u.left not in bool_updates
            }

            unrestricted_numeric_directions = {}
            monotonicity_antecedent = conjunct_formula_set(
                [t.condition]
                + self._actions_as_next_equalities(base_actions)
                + list(mg_preds)
            )
            for u in unrestricted_updates:
                v = u.left
                if self.symbol_table[str(v)] == BOOLEAN or v in const_choice_updates:
                    continue
                next_v = Variable(v.name + "'")
                implies_non_decreasing = self._antecedent_implies(
                    monotonicity_antecedent, BiOp(next_v, ">=", v)
                )
                implies_non_increasing = self._antecedent_implies(
                    monotonicity_antecedent, BiOp(next_v, "<=", v)
                )
                if implies_non_decreasing and not implies_non_increasing:
                    unrestricted_numeric_directions[v] = "inc"
                elif implies_non_increasing and not implies_non_decreasing:
                    unrestricted_numeric_directions[v] = "dec"

            direct_unrestricted_vars = set()
            if one_step_const_var is None:
                unrestricted_numeric_vars = {
                    u.left
                    for u in unrestricted_updates
                    if self.symbol_table[str(u.left)] != BOOLEAN
                    and u.left not in const_choice_updates
                }
                unrestricted_numeric_var_names = {
                    self._strip_prev_suffix(str(v)) for v in unrestricted_numeric_vars
                }
                current_unrestricted_var_names_in_preds = {
                    self._strip_prev_suffix(str(vv))
                    for p in mg_preds
                    for vv in p.variablesin()
                    if not vv.is_next()
                } & unrestricted_numeric_var_names
                current_unrestricted_var_names_in_ltl_mixed = (
                    unrestricted_numeric_var_names
                    & ltl_unprimed_related_to_primed_names
                )
                if (
                    len(current_unrestricted_var_names_in_preds) == 0
                    and len(current_unrestricted_var_names_in_ltl_mixed) == 0
                ):
                    direct_unrestricted_vars = unrestricted_numeric_vars

            self._bump_optimisation_counter(
                "minigame_only_inc_or_dec_vars",
                sum(1 for _, tt in restricted_updates if tt in {"inc", "dec"})
                + len(unrestricted_numeric_directions),
            )
            self._bump_optimisation_counter(
                "minigame_not_using_int_vars",
                len(direct_unrestricted_vars),
            )
            self._bump_optimisation_counter(
                "minigame_constant_update_vars",
                1 if one_step_const_var is not None else len(const_choice_updates),
            )

            if one_step_const_var is None:
                for u in unrestricted_updates:
                    v = u.left
                    if self.symbol_table[str(v)] == BOOLEAN:
                        continue
                    if v in const_choice_updates or v in direct_unrestricted_vars:
                        to_replace_preds[Variable(v.name + "'")] = v
                        continue
                    int_v = Variable("int_" + str(v))
                    self.symbol_table.update({str(int_v): INTEGER})
                    to_replace_preds[Variable(v.name + "'")] = int_v

            # For vars already updated directly in minigame actions (restricted
            # inc/dec/equality cases), interpret v' in stop predicates as the
            # current v under the chosen action.
            for u, _ in restricted_updates:
                to_replace_preds.setdefault(Variable(u.left.name + "'"), u.left)

            raw_events = []
            if one_step_const_var is not None:
                for c in one_step_consts:
                    raw_events.append(
                        f"{one_step_const_var.name}_set_{self._event_const_label(c)}"
                    )
                raw_events.append(f"{one_step_const_var.name}_set_other")
            else:
                for upd, _ in restricted_updates:
                    raw_events.append(upd.left.name + "_modify")
                for upd in unrestricted_updates:
                    if upd.left in const_choice_updates:
                        for c in const_choice_updates[upd.left]:
                            raw_events.append(
                                f"{upd.left.name}_set_{self._event_const_label(c)}"
                            )
                        raw_events.append(f"{upd.left.name}_set_other")
                    else:
                        direction = unrestricted_numeric_directions.get(upd.left)
                        if direction == "inc":
                            raw_events.append(upd.left.name + "_inc")
                        elif direction == "dec":
                            raw_events.append(upd.left.name + "_dec")
                        else:
                            raw_events.extend(
                                [upd.left.name + "_inc", upd.left.name + "_dec"]
                            )
                raw_events.append("stop")

            stop_prop = conjunct_formula_set(
                p.replace_formulas(to_replace_preds).simplify() for p in mg_preds
            )
            # Outside one-step-constant handling, all primed vars must now be
            # resolved either by deterministic substitutions or minigame int/current
            # proxies. If not, fail early with context.
            if one_step_const_var is None:
                residual_next = {
                    v
                    for v in stop_prop.variablesin()
                    if isinstance(v, Variable) and v.is_next()
                }
                unresolved_next = {
                    v for v in residual_next if v not in nondet_next_vars
                }
                if len(unresolved_next) > 0:
                    raise Exception(
                        "Unresolved primed vars in minigame stop predicate: "
                        + ", ".join(sorted(str(v) for v in unresolved_next))
                        + "\ntransition="
                        + str(t)
                        + "\nstop_pred="
                        + str(stop_prop)
                    )
            minigame_params = (undetermined_vars, mg_preds_key)
            if end_state in existing_mini_games_from_with:
                if minigame_params in existing_mini_games_from_with[end_state]:
                    start_state = existing_mini_games_from_with[end_state][
                        minigame_params
                    ]
                else:
                    existing_mini_games_from_with[end_state][
                        minigame_params
                    ] = start_state
            else:
                existing_mini_games_from_with[end_state] = {
                    minigame_params: start_state
                }

            con_bin_vars, bin_map = binary_rep(raw_events, "minigame_event_")
            to_replace = {}
            current_con_events = list(
                set(self.program.con_events) | self.new_con_events
            )
            vars_to_reuse = (
                len(con_bin_vars)
                if len(current_con_events) >= len(con_bin_vars)
                else len(current_con_events)
            )
            for i in range(vars_to_reuse):
                to_replace[con_bin_vars[i]] = current_con_events[i][0]
                con_bin_vars[i] = current_con_events[i][0]

            bin_map = {k: v.replace_formulas(to_replace) for k, v in bin_map.items()}
            stop = bin_map["stop"] if "stop" in bin_map else None
            self.new_con_events.update({(var, BOOLEAN) for var in con_bin_vars})
            for var in con_bin_vars:
                self.symbol_table[str(var)] = BOOLEAN

            no_mini_games_added_here = True
            if one_step_const_var is not None:
                no_mini_games_added = False
                no_mini_games_added_here = False
                v = one_step_const_var
                undet_vars.append(v)

                next_v = Variable(v.name + "'")
                for c in one_step_consts:
                    event_key = f"{v.name}_set_{self._event_const_label(c)}"
                    set_guard = conjunct(
                        bin_map[event_key],
                        conjunct_formula_set(
                            p.replace_formulas({next_v: Value(c)}) for p in mg_preds
                        ),
                    )
                    if sat(set_guard, self.symbol_table):
                        new_trans.append(
                            Transition(
                                start_state,
                                set_guard,
                                [Update(v, Value(c))],
                                [],
                                end_state,
                            )
                        )

                other_const = self._pick_other_constant(set(one_step_consts))
                other_guard = conjunct(
                    bin_map[f"{v.name}_set_other"],
                    conjunct_formula_set(
                        p.replace_formulas({next_v: Value(other_const)})
                        for p in mg_preds
                    ),
                )
                if sat(other_guard, self.symbol_table):
                    new_trans.append(
                        Transition(
                            start_state,
                            other_guard,
                            [Update(v, Value(other_const))],
                            [],
                            end_state,
                        )
                    )
            else:
                for u, typ in restricted_updates:
                    v = u.left
                    undet_vars.append(v)

                    modify_prop = bin_map[(v.name + "_modify")]
                    new_t.action.append(u)

                    if typ is None:
                        continue
                    no_mini_games_added = False
                    no_mini_games_added_here = False

                    if typ == "inc":
                        modify_t = Transition(
                            start_state,
                            modify_prop,
                            [Update(u.left, BiOp(u.left, "+", Value(1)))],
                            [],
                            start_state,
                        )
                    elif typ == "dec":
                        modify_t = Transition(
                            start_state,
                            modify_prop,
                            [Update(u.left, BiOp(u.left, "-", Value(1)))],
                            [],
                            start_state,
                        )
                    else:
                        raise Exception("Unknown transition type: " + str(typ))

                    stop_t = Transition(start_state, stop, [], [], end_state)
                    new_trans.append(modify_t)
                    new_trans.append(stop_t)

                unrestricted_non_det_vars = []
                for u in unrestricted_updates:
                    no_mini_games_added = False
                    no_mini_games_added_here = False
                    v = u.left
                    undet_vars.append(v)
                    if v not in const_choice_updates:
                        unrestricted_non_det_vars.append(v)

                    if v in const_choice_updates:
                        for c in const_choice_updates[v]:
                            event_key = f"{v.name}_set_{self._event_const_label(c)}"
                            new_trans.append(
                                Transition(
                                    start_state,
                                    bin_map[event_key],
                                    [Update(v, Value(c))],
                                    [],
                                    start_state,
                                )
                            )
                        other_c = self._pick_other_constant(
                            set(const_choice_updates[v])
                        )
                        other_event = f"{v.name}_set_other"
                        new_trans.append(
                            Transition(
                                start_state,
                                bin_map[other_event],
                                [Update(v, Value(other_c))],
                                [],
                                start_state,
                            )
                        )
                        continue

                    direction = unrestricted_numeric_directions.get(v)
                    inc_prop = (
                        bin_map[(v.name + "_inc")]
                        if (v.name + "_inc") in bin_map
                        else None
                    )
                    dec_prop = (
                        bin_map[(v.name + "_dec")]
                        if (v.name + "_dec") in bin_map
                        else None
                    )

                    if v in bool_updates:
                        if inc_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    inc_prop,
                                    [Update(v, Value(BoolAtoms.TRUE))],
                                    [],
                                    start_state,
                                )
                            )
                        if dec_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    dec_prop,
                                    [Update(v, Value(BoolAtoms.FALSE))],
                                    [],
                                    start_state,
                                )
                            )
                    elif v in direct_unrestricted_vars:
                        stutter_guard = conjunct(stop, neg(stop_prop))
                        if sat(stutter_guard, self.symbol_table):
                            new_trans.append(
                                Transition(
                                    start_state, stutter_guard, [], [], start_state
                                )
                            )
                        if direction != "dec" and inc_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    inc_prop,
                                    [Update(v, BiOp(v, "+", Value(1)))],
                                    [],
                                    start_state,
                                )
                            )
                        if direction != "inc" and dec_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    dec_prop,
                                    [Update(v, BiOp(v, "-", Value(1)))],
                                    [],
                                    start_state,
                                )
                            )
                    else:
                        int_v = Variable("int_" + str(v))
                        to_add_to_local_vars.add((v, int_v))
                        new_t.action.append(Update(int_v, v))
                        new_t.action.append(Update(v, v))
                        stutter_guard = conjunct(stop, neg(stop_prop))
                        if sat(stutter_guard, self.symbol_table):
                            new_trans.append(
                                Transition(
                                    start_state, stutter_guard, [], [], start_state
                                )
                            )
                        if direction != "dec" and inc_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    inc_prop,
                                    [Update(int_v, BiOp(int_v, "+", Value(1)))],
                                    [],
                                    start_state,
                                )
                            )
                        if direction != "inc" and dec_prop is not None:
                            new_trans.append(
                                Transition(
                                    start_state,
                                    dec_prop,
                                    [Update(int_v, BiOp(int_v, "-", Value(1)))],
                                    [],
                                    start_state,
                                )
                            )

                if len(unrestricted_updates) > 0:
                    stop_guard = conjunct(stop, stop_prop)
                    if sat(stop_guard, self.symbol_table):
                        stop_t = Transition(
                            start_state,
                            stop_guard,
                            [
                                Update(v, Variable("int_" + str(v)))
                                for v in unrestricted_non_det_vars
                                if v not in bool_updates
                                and v not in direct_unrestricted_vars
                            ],
                            [],
                            end_state,
                        )
                        new_trans.append(stop_t)

            if not no_mini_games_added_here:
                mini_game_counter += 1
            new_trans.append(new_t)

        if no_mini_games_added:
            return self._finalise_no_minigame_program(
                new_trans=new_trans,
                minigame_states=minigame_states,
                normalise_losing=normalise_losing,
                extra_local_init_values=curr_state_init_values,
            )

        new_init_var_values = {
            (
                str(int_v),
                self.program.symbol_table[str(v)],
                Value(0) if v not in bool_updates else Value(False),
            )
            for v, int_v in to_add_to_local_vars
        }

        self._assert_no_conflicting_transitions(
            new_trans, self.symbol_table, minigame_states, self.new_con_events
        )

        return self._finalise_with_minigames_program(
            new_trans=new_trans,
            minigame_states=minigame_states,
            new_states=new_states,
            new_init_var_values=new_init_var_values,
            extra_local_init_values=curr_state_init_values,
            normalise_losing=normalise_losing,
        )
