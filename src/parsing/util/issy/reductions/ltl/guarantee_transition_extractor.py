import itertools
import logging
from dataclasses import dataclass

import config
from parsing.util.issy.reductions.ltl.formula_utils import _TEMPORAL_OPS
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.types import BOOLEAN
from prop_lang.update import Update
from prop_lang.uniop import UniOp
from prop_lang.util import (
    atomic_predicates,
    conjunct_formula_set,
    disjunct_formula_set,
    extract_initial_formula,
    false,
    neg,
    sat,
    true,
    is_tautology,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


@dataclass(frozen=True)
class _GuaranteeUpdateRule:
    guard: Formula
    updates: tuple[Update, ...]


@dataclass(frozen=True)
class _GuaranteeCandidateGroup:
    candidates: tuple[_GuaranteeUpdateRule, ...]


@dataclass
class GuaranteeTransitionExtractionResult:
    transitions: list[Transition]
    rewritten_objectives: list[Formula]
    extracted_rule_count: int
    extracted_formula_count: int
    new_controller_props: tuple[Variable, ...] = ()
    skipped_reason: str | None = None

    @property
    def applied(self) -> bool:
        return len(self.transitions) > 0 and self.extracted_formula_count > 0


def _formula_is_temporal(formula: Formula) -> bool:
    q = formula
    return any(op in _TEMPORAL_OPS for op in q.ops_used())


class IssyGuaranteeTransitionExtractor:
    """
    Extract transition-style guarantees from formula-only ISSY objectives.

    This pass intentionally extracts only from *guarantees*:
    - If a formula is `A -> B`, only `B` is scanned for extractable transitions.
    - Assumption-side formulas are never converted into transitions.

    Supported pattern (strict and conservative):
    - global guarantee clauses of the form `G(g -> us)` or `G(us)`, where:
      - `g` is a state/input guard (no temporal ops, no next vars),
      - `us` is a conjunction of one-step deterministic updates:
        `x' = rhs` (or `X(x = rhs)`), plus boolean shorthands
        (`x'`, `!x'`, `X(x)`, `X(!x)`).

    The extractor builds a guard-partitioned transition set by considering
    combinations of extracted guards and composing compatible updates.
    If conflicting update requirements are possible on an overlap region,
    extraction is aborted.
    """

    def __init__(
        self,
        symbol_table: dict[str, object],
        allowed_update_var_names: set[str],
        *,
        eval_state: str = "eval",
        max_partition_rules: int = 8,
    ):
        self.allowed_update_var_names = set(allowed_update_var_names)
        self.eval_state = eval_state
        self.max_partition_rules = max(1, int(max_partition_rules))
        self._guard_next_var_to_con_prop: dict[str, Variable] = {}
        self._guard_con_prop_names: set[str] = set()
        # Keep extraction-side symbol edits local; caller should only commit
        # controller props when extraction is actually applied.
        self.symbol_table = dict(symbol_table)

    def extract(
        self,
        objectives: list[Formula],
    ) -> GuaranteeTransitionExtractionResult:
        self._debug_extracted_group_contexts: list[
            tuple[_GuaranteeCandidateGroup, Formula]
        ] = []
        candidate_groups: list[_GuaranteeCandidateGroup] = []
        extracted_formula_count = 0
        rewritten = []
        for obj in objectives:
            new_obj, groups, removed_count = self._rewrite_objective(obj)
            rewritten.append(new_obj)
            candidate_groups.extend(groups)
            extracted_formula_count += removed_count

        if extracted_formula_count == 0 or len(candidate_groups) == 0:
            return GuaranteeTransitionExtractionResult(
                transitions=[],
                rewritten_objectives=list(objectives),
                extracted_rule_count=0,
                extracted_formula_count=0,
                new_controller_props=(),
            )

        reason = None

        unique_groups = self._dedupe_groups(candidate_groups)
        if len(unique_groups) > self.max_partition_rules:
            reason = (
                "too_many_rules_for_partition("
                + str(len(unique_groups))
                + ">"
                + str(self.max_partition_rules)
                + ")"
            )
        else:
            transitions, conflict = self._build_partitioned_transitions(unique_groups)
            if conflict or len(transitions) == 0:
                reason = (
                    "conflicting_updates_on_overlapping_guards"
                    if conflict
                    else "no_satisfiable_guard_partitions"
                )

        if reason:
            return GuaranteeTransitionExtractionResult(
                transitions=[],
                rewritten_objectives=list(objectives),
                extracted_rule_count=0,
                extracted_formula_count=0,
                new_controller_props=(),
                skipped_reason=reason,
            )

        self._debug_assert_rewrite_spot_equivalent(
            original_objectives=objectives,
            rewritten_objectives=rewritten,
            extracted_group_contexts=self._debug_extracted_group_contexts,
        )

        return GuaranteeTransitionExtractionResult(
            transitions=transitions,
            rewritten_objectives=rewritten,
            extracted_rule_count=extracted_formula_count,
            extracted_formula_count=extracted_formula_count,
            new_controller_props=tuple(
                sorted(self._guard_next_var_to_con_prop.values(), key=lambda v: v.name)
            ),
        )

    def _rewrite_objective(
        self, formula: Formula
    ) -> tuple[Formula, list[_GuaranteeCandidateGroup], int]:
        objective_unprimed_vars = {
            str(v)
            for v in formula.variablesin()
            if isinstance(v, Variable) and not v.is_next()
        }
        return self._extract_transition_formulas(
            formula, objective_unprimed_vars, true()
        )

    def _extract_transition_formulas(
        self,
        formula: Formula,
        objective_unprimed_vars: set[str],
        extraction_context: Formula,
    ) -> tuple[Formula, list[_GuaranteeCandidateGroup], int]:
        # extracts transition formulas from guarantees, if assumptions are initial-only
        q = formula
        if isinstance(q, BiOp) and q.op == "&":
            l_new, l_rules, l_removed = self._extract_transition_formulas(
                q.left,
                objective_unprimed_vars,
                extraction_context,
            )
            r_new, r_rules, r_removed = self._extract_transition_formulas(
                q.right,
                objective_unprimed_vars,
                extraction_context,
            )
            return (
                BiOp(l_new, q.op, r_new).simplify(),
                l_rules + r_rules,
                l_removed + r_removed,
            )

        if isinstance(q, BiOp) and q.op == "->":
            antecedent = q.left
            antecedent_is_true = isinstance(antecedent, Value) and antecedent.is_true()
            antecedent_init = extract_initial_formula(antecedent)
            antecedent_is_initial = antecedent_init is not None and str(
                antecedent_init
            ) == str(antecedent)
            if not (antecedent_is_true or antecedent_is_initial):
                return q, [], 0

            new_right, rules, removed = self._extract_transition_formulas(
                q.right,
                objective_unprimed_vars,
                conjunct_formula_set([extraction_context, antecedent]).simplify(),
            )
            return BiOp(q.left, q.op, new_right).simplify(), rules, removed

        return self._rewrite_guarantee_formula(
            q, objective_unprimed_vars, extraction_context
        )

    def _rewrite_guarantee_formula(
        self,
        formula: Formula,
        objective_unprimed_vars: set[str],
        extraction_context: Formula,
    ) -> tuple[Formula, list[_GuaranteeCandidateGroup], int]:
        q = formula
        if isinstance(q, BiOp) and q.op == "&":
            l_new, l_rules, l_removed = self._rewrite_guarantee_formula(
                q.left, objective_unprimed_vars, extraction_context
            )
            r_new, r_rules, r_removed = self._rewrite_guarantee_formula(
                q.right, objective_unprimed_vars, extraction_context
            )
            return (
                BiOp(l_new, q.op, r_new).simplify(),
                l_rules + r_rules,
                l_removed + r_removed,
            )

        group = self._extract_rules_from_global_guarantee(q, objective_unprimed_vars)
        if group is None:
            return q, [], 0
        self._debug_extracted_group_contexts.append((group, extraction_context))
        return true(), [group], 1

    def _extract_rules_from_global_guarantee(
        self, q: Formula, objective_unprimed_vars: set[str]
    ) -> _GuaranteeCandidateGroup | None:
        if not isinstance(q, UniOp) or q.op != "G":
            return None

        body = q.right
        if isinstance(body, BiOp) and body.op == "->":
            guard_raw = body.left
            update_formula = body.right
            is_implication = True
        else:
            guard_raw = true()
            update_formula = body
            is_implication = False

        # If the implication antecedent is a pure next-boolean constraint,
        # encode it as update branching (not as a current-state guard).
        if is_implication and self._is_boolean_next_constraint_formula(guard_raw):
            update_branches = self._parse_update_formula(
                update_formula, temporal_depth=0
            )
            if update_branches is not None:
                false_maps = self._satisfying_minterm_update_maps(neg(guard_raw))
                true_maps = self._satisfying_minterm_update_maps(guard_raw)
                candidates = []
                for false_map in false_maps:
                    updates = tuple(
                        Update(Variable(var_name), rhs)
                        for var_name, rhs in sorted(
                            false_map.items(), key=lambda item: item[0]
                        )
                    )
                    candidates.append(
                        _GuaranteeUpdateRule(guard=true(), updates=updates)
                    )
                for true_map in true_maps:
                    for us_map in update_branches:
                        merged = self._merge_update_maps(true_map, us_map)
                        if merged is None:
                            continue
                        updates = tuple(
                            Update(Variable(var_name), rhs)
                            for var_name, rhs in sorted(
                                merged.items(), key=lambda item: item[0]
                            )
                        )
                        candidates.append(
                            _GuaranteeUpdateRule(guard=true(), updates=updates)
                        )
                candidates = self._dedupe_rules(candidates)
                if len(candidates) > 0:
                    return _GuaranteeCandidateGroup(candidates=tuple(candidates))

        # Constraint-only guarantees over next booleans are also update constraints.
        if not is_implication and self._is_boolean_next_constraint_formula(
            update_formula
        ):
            update_maps = self._satisfying_minterm_update_maps(update_formula)
            candidates = []
            for update_map in update_maps:
                updates = tuple(
                    Update(Variable(var_name), rhs)
                    for var_name, rhs in sorted(
                        update_map.items(), key=lambda item: item[0]
                    )
                )
                candidates.append(_GuaranteeUpdateRule(guard=true(), updates=updates))
            candidates = self._dedupe_rules(candidates)
            if len(candidates) > 0:
                return _GuaranteeCandidateGroup(candidates=tuple(candidates))

        tentative_guard_next_map: dict[str, Variable] = {}
        tentative_guard_names: set[str] = set()
        guard = self._rewrite_guard_formula(
            guard_raw,
            objective_unprimed_vars,
            tentative_guard_next_map,
            tentative_guard_names,
        )
        if guard is None:
            return None

        parsed = self._parse_update_formula(update_formula, temporal_depth=0)
        if parsed is not None:
            candidates = []
            if sat(neg(guard), self.symbol_table):
                candidates.append(
                    _GuaranteeUpdateRule(guard=neg(guard), updates=tuple())
                )
            for parsed_updates in parsed:
                updates = tuple(
                    Update(Variable(var_name), rhs)
                    for var_name, rhs in sorted(
                        parsed_updates.items(), key=lambda item: item[0]
                    )
                )
                candidates.append(_GuaranteeUpdateRule(guard=guard, updates=updates))
            candidates = self._dedupe_rules(candidates)
            if len(candidates) > 0:
                self._commit_guard_controller_props(
                    tentative_guard_next_map, tentative_guard_names
                )
                return _GuaranteeCandidateGroup(candidates=tuple(candidates))

        # Constraint-only global guarantees with next literals (e.g. G(!r0' || !r1'))
        # should also contribute to candidate composition, otherwise mutually exclusive
        # next-guard constraints are lost and can create artificial update conflicts.
        if not is_implication and self._is_boolean_guard_constraint_formula(
            update_formula
        ):
            guard_only = self._rewrite_guard_formula(
                update_formula,
                objective_unprimed_vars,
                tentative_guard_next_map,
                tentative_guard_names,
            )
            if guard_only is not None:
                minterm_guards = self._satisfying_minterm_guards(guard_only)
                if len(minterm_guards) > 0:
                    self._commit_guard_controller_props(
                        tentative_guard_next_map, tentative_guard_names
                    )
                    return _GuaranteeCandidateGroup(
                        candidates=tuple(
                            _GuaranteeUpdateRule(guard=g, updates=tuple())
                            for g in minterm_guards
                        )
                    )
        return None

    def _is_boolean_guard_constraint_formula(self, formula: Formula) -> bool:
        q = formula
        if any(op in _TEMPORAL_OPS for op in q.ops_used()):
            return False
        vars_in_formula = [v for v in q.variablesin() if isinstance(v, Variable)]
        if len(vars_in_formula) == 0:
            return False
        for v in vars_in_formula:
            v_name = str(v.prev_rep()) if v.is_next() else str(v)
            if self.symbol_table.get(v_name) != BOOLEAN:
                return False
        return True

    def _is_boolean_next_constraint_formula(self, formula: Formula) -> bool:
        q = formula
        if any(op in _TEMPORAL_OPS for op in q.ops_used()):
            return False
        vars_in_formula = [v for v in q.variablesin() if isinstance(v, Variable)]
        if len(vars_in_formula) == 0:
            return False
        for v in vars_in_formula:
            if not v.is_next():
                return False
            base_name = str(v.prev_rep())
            if self.symbol_table.get(base_name) != BOOLEAN:
                return False
        return True

    def _satisfying_minterm_update_maps(
        self, formula: Formula
    ) -> list[dict[str, Formula]]:
        q = formula
        vars_in_formula = sorted(
            {
                v
                for v in q.variablesin()
                if isinstance(v, Variable)
                and v.is_next()
                and self.symbol_table.get(str(v.prev_rep())) == BOOLEAN
            },
            key=lambda v: v.name,
        )
        if len(vars_in_formula) == 0:
            return []

        maps: list[dict[str, Formula]] = []
        for bits in itertools.product([False, True], repeat=len(vars_in_formula)):
            lits = []
            update_map: dict[str, Formula] = {}
            valid_map = True
            for i, bit in enumerate(bits):
                v = vars_in_formula[i]
                lits.append(v if bit else neg(v))
                target = str(v.prev_rep())
                if target not in self.allowed_update_var_names:
                    valid_map = False
                    break
                update_map[target] = true() if bit else false()
            if not valid_map:
                continue
            cube = conjunct_formula_set(lits).simplify()
            guarded = conjunct_formula_set([q, cube]).simplify()
            if sat(guarded, self.symbol_table):
                maps.append(update_map)

        deduped = []
        seen = set()
        for m in maps:
            key = tuple(sorted((k, str(v)) for k, v in m.items()))
            if key in seen:
                continue
            seen.add(key)
            deduped.append(m)
        return deduped

    def _satisfying_minterm_guards(self, formula: Formula) -> list[Formula]:
        q = formula
        vars_in_formula = sorted(
            {
                v
                for v in q.variablesin()
                if isinstance(v, Variable) and self.symbol_table.get(str(v)) == BOOLEAN
            },
            key=lambda v: v.name,
        )
        if len(vars_in_formula) == 0:
            return [q] if sat(q, self.symbol_table) else []

        cubes = []
        for bits in itertools.product([False, True], repeat=len(vars_in_formula)):
            lits = []
            for i, bit in enumerate(bits):
                v = vars_in_formula[i]
                lits.append(v if bit else neg(v))
            cube = conjunct_formula_set(lits).simplify()
            guarded = conjunct_formula_set([q, cube]).simplify()
            if sat(guarded, self.symbol_table):
                cubes.append(cube)
        return cubes

    def _is_state_guard_formula(
        self, formula: Formula, *, allow_next_bool: bool
    ) -> bool:
        q = formula
        if any(op in _TEMPORAL_OPS for op in q.ops_used()):
            return False
        next_vars = [
            v for v in q.variablesin() if isinstance(v, Variable) and v.is_next()
        ]
        if not allow_next_bool and len(next_vars) > 0:
            return False
        if allow_next_bool:
            for v in next_vars:
                base = str(v.prev_rep())
                if base not in self.symbol_table or self.symbol_table[base] != BOOLEAN:
                    return False
        return True

    def _rewrite_guard_formula(
        self,
        formula: Formula,
        objective_unprimed_vars: set[str],
        tentative_guard_next_map: dict[str, Variable],
        tentative_guard_names: set[str],
    ) -> Formula | None:
        q = formula
        if not self._is_state_guard_formula(q, allow_next_bool=True):
            return None

        failed = False

        def _replace(node: Formula):
            nonlocal failed
            qq = node
            if not isinstance(qq, Variable) or not qq.is_next():
                return None
            base_name = str(qq.prev_rep())
            if base_name in objective_unprimed_vars:
                failed = True
                return qq
            if (
                base_name not in self.symbol_table
                or self.symbol_table[base_name] != BOOLEAN
            ):
                failed = True
                return qq
            return self._guard_controller_prop_for_next_var(
                qq,
                tentative_guard_next_map,
                tentative_guard_names,
            )

        rewritten = q.replace_formulas(_replace).simplify()
        if failed:
            return None
        if not self._is_state_guard_formula(rewritten, allow_next_bool=False):
            return None
        return rewritten

    def _guard_controller_prop_for_next_var(
        self,
        next_var: Variable,
        tentative_guard_next_map: dict[str, Variable],
        tentative_guard_names: set[str],
    ) -> Variable:
        key = str(next_var)
        if key in self._guard_next_var_to_con_prop:
            return self._guard_next_var_to_con_prop[key]
        if key in tentative_guard_next_map:
            return tentative_guard_next_map[key]

        base = str(next_var.prev_rep())
        name = f"guard_next_{base}"
        idx = 0
        while (
            name in self.symbol_table
            or name in self._guard_con_prop_names
            or name in tentative_guard_names
        ):
            idx += 1
            name = f"guard_next_{base}_{idx}"

        v = Variable(name)
        tentative_guard_next_map[key] = v
        tentative_guard_names.add(name)
        return v

    def _commit_guard_controller_props(
        self,
        tentative_guard_next_map: dict[str, Variable],
        tentative_guard_names: set[str],
    ) -> None:
        if len(tentative_guard_next_map) == 0:
            return
        self._guard_next_var_to_con_prop.update(tentative_guard_next_map)
        self._guard_con_prop_names.update(tentative_guard_names)
        for name in tentative_guard_names:
            self.symbol_table[name] = BOOLEAN

    def _parse_update_formula(
        self,
        formula: Formula,
        *,
        temporal_depth: int,
    ) -> list[dict[str, Formula]] | None:
        q = formula
        if isinstance(q, BiOp) and q.op == "&":
            left = self._parse_update_formula(q.left, temporal_depth=temporal_depth)
            if left is None:
                return None
            right = self._parse_update_formula(q.right, temporal_depth=temporal_depth)
            if right is None:
                return None
            merged = []
            for l in left:
                for r in right:
                    m = self._merge_update_maps(l, r)
                    if m is not None:
                        merged.append(m)
            if len(merged) == 0:
                return None
            return merged

        if isinstance(q, BiOp) and q.op == "|":
            left = self._parse_update_formula(q.left, temporal_depth=temporal_depth)
            right = self._parse_update_formula(q.right, temporal_depth=temporal_depth)
            if left is None and right is None:
                return None
            if left is None:
                return right
            if right is None:
                return left
            return left + right

        if isinstance(q, UniOp) and q.op == "X":
            if temporal_depth >= 1:
                return None
            return self._parse_update_formula(
                q.right, temporal_depth=temporal_depth + 1
            )

        assignment = self._parse_assignment_atom(q, temporal_depth=temporal_depth)
        if assignment is None:
            return None
        return [assignment]

    def _parse_assignment_atom(
        self, atom: Formula, *, temporal_depth: int
    ) -> dict[str, Formula] | None:
        q = atom

        if isinstance(q, Value):
            if q.is_true():
                return {}
            return None

        if isinstance(q, Variable):
            target = self._target_var_name_for_literal(q, temporal_depth)
            if target is None:
                return None
            return {target: true()}

        if isinstance(q, UniOp) and q.op == "!" and isinstance((q.right), Variable):
            var = q.right
            target = self._target_var_name_for_literal(var, temporal_depth)
            if target is None:
                return None
            return {target: false()}

        if not isinstance(q, BiOp) or q.op != "=":
            return None

        left = q.left
        right = q.right
        parsed = self._parse_assignment_from_equality(
            left, right, temporal_depth=temporal_depth
        )
        if parsed is not None:
            return parsed
        return self._parse_assignment_from_equality(
            right, left, temporal_depth=temporal_depth
        )

    def _parse_assignment_from_equality(
        self,
        lhs: Formula,
        rhs: Formula,
        *,
        temporal_depth: int,
    ) -> dict[str, Formula] | None:
        if not isinstance(lhs, Variable):
            return None
        target = self._target_var_name_for_literal(lhs, temporal_depth)
        if target is None:
            return None
        rhs_norm = rhs
        if _formula_is_temporal(rhs_norm):
            return None
        if any(isinstance(v, Variable) and v.is_next() for v in rhs_norm.variablesin()):
            return None
        return {target: rhs_norm}

    def _target_var_name_for_literal(
        self, var: Variable, temporal_depth: int
    ) -> str | None:
        if temporal_depth == 0:
            if not var.is_next():
                return None
            target = var.prev_rep().name
        elif temporal_depth == 1:
            if var.is_next():
                return None
            target = var.name
        else:
            return None

        if target not in self.allowed_update_var_names:
            return None
        return target

    def _merge_update_maps(
        self, left: dict[str, Formula], right: dict[str, Formula]
    ) -> dict[str, Formula] | None:
        out = dict(left)
        for var_name, rhs in right.items():
            if var_name not in out:
                out[var_name] = rhs
                continue
            if not self._rhs_equivalent(out[var_name], rhs):
                return None
        return out

    def _rhs_equivalent(self, lhs: Formula, rhs: Formula) -> bool:
        lhs_n = lhs
        rhs_n = rhs
        if str(lhs_n) == str(rhs_n):
            return True
        try:
            return is_tautology(BiOp(lhs_n, "=", rhs_n), self.symbol_table)
        except Exception:
            return False

    def _dedupe_rules(
        self, rules: list[_GuaranteeUpdateRule]
    ) -> list[_GuaranteeUpdateRule]:
        by_key = {}
        for rule in rules:
            update_key = tuple(sorted(str(u) for u in rule.updates))
            key = (str(rule.guard), update_key)
            by_key[key] = rule
        return [by_key[k] for k in sorted(by_key.keys(), key=str)]

    def _dedupe_groups(
        self, groups: list[_GuaranteeCandidateGroup]
    ) -> list[_GuaranteeCandidateGroup]:
        by_key = {}
        for g in groups:
            key = tuple(
                sorted(
                    (str(c.guard), tuple(sorted(str(u) for u in c.updates)))
                    for c in g.candidates
                )
            )
            by_key[key] = g
        return [by_key[k] for k in sorted(by_key.keys(), key=str)]

    def _debug_assert_rewrite_spot_equivalent(
        self,
        *,
        original_objectives: list[Formula],
        rewritten_objectives: list[Formula],
        extracted_group_contexts: list[tuple[_GuaranteeCandidateGroup, Formula]],
    ) -> None:
        if not config.Config.getConfig().debug:
            return
        if len(extracted_group_contexts) == 0:
            return

        original_formula = conjunct_formula_set(original_objectives).simplify()
        reconstructed_formula = conjunct_formula_set(
            rewritten_objectives
            + self._rebuild_ltl_from_extracted_groups_with_context(
                extracted_group_contexts
            )
        ).simplify()
        if self._spot_are_equivalent(original_formula, reconstructed_formula):
            return
        raise RuntimeError(
            "Guarantee extraction rewrite is not Spot-equivalent.\n\n"
            + str(original_formula)
            + "\nvs\n"
            + str(reconstructed_formula)
        )

    def _rebuild_ltl_from_extracted_groups_with_context(
        self, extracted_group_contexts: list[tuple[_GuaranteeCandidateGroup, Formula]]
    ) -> list[Formula]:
        rebuilt: list[Formula] = []
        for group, context in extracted_group_contexts:
            branch_formulas: list[Formula] = []
            for candidate in group.candidates:
                update_atoms = [
                    BiOp(Variable(str(update.left) + "'"), "=", update.right)
                    for update in candidate.updates
                ]
                branch_formulas.append(
                    conjunct_formula_set([candidate.guard] + update_atoms).simplify()
                )
            extracted_formula = UniOp(
                "G", disjunct_formula_set(branch_formulas).simplify()
            ).simplify()
            if isinstance(context, Value) and context.is_true():
                rebuilt.append(extracted_formula)
            else:
                rebuilt.append(BiOp(context, "->", extracted_formula).simplify())
        return rebuilt

    def _spot_are_equivalent(self, left: Formula, right: Formula) -> bool:
        try:
            import spot
        except Exception as err:  # pragma: no cover
            raise RuntimeError(
                "Debug Spot equivalence check requires python-spot: " + repr(err)
            ) from err

        left_norm = self._normalize_boolean_equalities_for_spot(left).simplify()
        right_norm = self._normalize_boolean_equalities_for_spot(right).simplify()

        atom_to_ap = self._spot_atom_to_ap([left_norm, right_norm])
        left_ap = self._replace_atoms_with_aps(left_norm, atom_to_ap)
        right_ap = self._replace_atoms_with_aps(right_norm, atom_to_ap)

        left_text = str(left_ap).replace("TRUE", "true").replace("FALSE", "false")
        right_text = str(right_ap).replace("TRUE", "true").replace("FALSE", "false")
        return spot.are_equivalent(spot.formula(left_text), spot.formula(right_text))

    @staticmethod
    def _normalize_boolean_equalities_for_spot(formula: Formula) -> Formula:
        def _replace(node: Formula):
            q = node
            if not isinstance(q, BiOp) or q.op != "=":
                return None

            left = q.left
            right = q.right

            if (
                isinstance(left, Variable)
                and isinstance(right, Value)
                and right.is_true()
            ):
                return left
            if (
                isinstance(left, Variable)
                and isinstance(right, Value)
                and right.is_false()
            ):
                return neg(left)
            if (
                isinstance(right, Variable)
                and isinstance(left, Value)
                and left.is_true()
            ):
                return right
            if (
                isinstance(right, Variable)
                and isinstance(left, Value)
                and left.is_false()
            ):
                return neg(right)
            return None

        return formula.replace_formulas(_replace)

    @staticmethod
    def _spot_atom_to_ap(formulas: list[Formula]) -> dict[str, str]:
        atom_keys = sorted(
            {str(atom) for formula in formulas for atom in atomic_predicates(formula)}
        )
        return {atom: f"p{i}" for i, atom in enumerate(atom_keys)}

    @staticmethod
    def _replace_atoms_with_aps(formula: Formula, atom_to_ap: dict[str, str]) -> Formula:
        def _replace(node: Formula):
            key = str(node)
            if key in atom_to_ap:
                return Variable(atom_to_ap[key])
            return None

        return formula.replace_formulas(_replace)

    def _build_partitioned_transitions(
        self, groups: list[_GuaranteeCandidateGroup]
    ) -> tuple[list[Transition], bool]:
        if len(groups) == 0:
            return [], False

        transitions = []
        seen = set()

        choice_spaces = [list(g.candidates) for g in groups]
        if any(len(cs) == 0 for cs in choice_spaces):
            return [], False

        saw_conflicting_combo = False
        for combo in itertools.product(*choice_spaces):
            conjuncts = [c.guard for c in combo]
            guard_region = conjunct_formula_set(conjuncts).simplify()
            if not sat(guard_region, self.symbol_table):
                continue

            update_map: dict[str, Formula] = {}
            conflict = False
            for candidate in combo:
                for u in candidate.updates:
                    var_name = str(u.left)
                    if var_name in update_map and not self._rhs_equivalent(
                        update_map[var_name], u.right
                    ):
                        conflict = True
                        break
                    update_map[var_name] = u.right
                if conflict:
                    break
            if conflict:
                saw_conflicting_combo = True
                continue

            actions = [
                Update(Variable(var_name), rhs)
                for var_name, rhs in sorted(
                    update_map.items(), key=lambda item: item[0]
                )
            ]
            key = (str(guard_region), tuple(str(a) for a in actions))
            if key in seen:
                continue
            seen.add(key)
            transitions.append(
                Transition(
                    self.eval_state,
                    guard_region,
                    actions,
                    [],
                    self.eval_state,
                )
            )

        transitions = sorted(transitions, key=str)
        logging.info(
            "ISSY guarantee-transition extraction: groups=%s, transitions=%s",
            len(groups),
            len(transitions),
        )
        if len(transitions) == 0 and saw_conflicting_combo:
            return [], True
        return transitions, False
