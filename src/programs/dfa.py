# This modules implements data-flow analyses for programs

from collections import defaultdict, deque
from typing import Any, Callable, Hashable, Optional, Set, Tuple

from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import BoolBiOps, MathRels
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import (
    normalize_ltl,
    propagate_negations,
    sat,
    simplify_formula_with_math_wo_type_constraints,
)
from prop_lang.value import Value
from prop_lang.variable import Variable

Context = Any
TransitionStep = Callable[[Hashable, Context, Transition], Context]
StopCondition = Callable[[Hashable, Context], bool]
KeyFn = Callable[[Hashable, Context], Hashable]
VisitFn = Callable[[Hashable, Context], None]
NeighborFn = Callable[[Hashable], list[Hashable]]
NodeVisitFn = Callable[[Hashable], None]
EdgeVisitFn = Callable[[Hashable, Hashable], None]


def program_bfs(
    program,
    initial_context: Context,
    step: TransitionStep,
    stop_condition: Optional[StopCondition] = None,
    key_fn: Optional[KeyFn] = None,
    on_visit: Optional[VisitFn] = None,
    from_state: Hashable = None,
) -> Set[Hashable]:
    """Generic BFS over the program's transition graph.

    The traversal starts from ``program.initial_state`` and propagates a mutable
    ``context`` using ``step``. ``stop_condition`` can prune branches early, and
    ``key_fn`` controls how visited states are memoised. Returns the set of
    visited keys (as produced by ``key_fn`` or the default ``(state, context)``).
    """
    if not from_state:
        from_state = program.initial_state
    queue = deque([(from_state, initial_context)])
    visited: Set[Hashable] = set()

    while queue:
        state, context = queue.popleft()
        key = key_fn(state, context) if key_fn else (state, context)
        if key in visited:
            continue
        visited.add(key)

        if on_visit:
            on_visit(state, context)

        if stop_condition and stop_condition(state, context):
            continue

        for transition in program.state_to_trans.get(state, []):
            queue.append((transition.tgt, step(state, context, transition)))

    return visited


def program_dfs(
    start_nodes: list[Hashable],
    neighbors: NeighborFn,
    on_enter: Optional[NodeVisitFn] = None,
    on_exit: Optional[NodeVisitFn] = None,
    visited: Optional[Set[Hashable]] = None,
) -> Set[Hashable]:
    """Generic DFS over an adjacency function, with optional enter/exit hooks."""

    if visited is None:
        visited = set()

    for start in start_nodes:
        if start in visited:
            continue

        visited.add(start)
        if on_enter:
            on_enter(start)

        stack: list[tuple[Hashable, Any]] = [(start, iter(neighbors(start)))]
        while stack:
            node, iterator = stack[-1]
            try:
                neighbor = next(iterator)
            except StopIteration:
                stack.pop()
                if on_exit:
                    on_exit(node)
                continue

            if neighbor in visited:
                continue

            visited.add(neighbor)
            if on_enter:
                on_enter(neighbor)
            stack.append((neighbor, iter(neighbors(neighbor))))

    return visited


def value_dependencies(program, init_state=None) -> Set[Variable]:
    """Return uninitialised variables whose initial values affect control flow.

    A variable's initial value matters if some reachable guard references it
    before any update to that variable executes along that path. Once a variable
    is updated or has triggered a guard reference, the search for that variable
    stops on the current branch to avoid redundant exploration.
    """

    uninitialised = {v for v in program.unset_init_vars}
    if not uninitialised:
        return set()

    matters: Set[str] = set()

    def step(_, context: Tuple[Set[str], Set[str]], transition: Transition):
        updated, seen_in_guard = context

        guard_vars = {
            v.name
            for v in transition.condition.variablesin()
            if v.name in uninitialised
        }
        used_in_variable_update = {
            v.name
            for action in transition.action
            for v in action.right.variablesin()
            if action.left != action.right and v.name in uninitialised
        }
        guard_before_update = (guard_vars | used_in_variable_update) - updated

        if guard_before_update:
            matters.update(guard_before_update)

        updated_now = updated | {
            action.left.name
            for action in transition.action
            if action.left.name in uninitialised and action.left != action.right
        }

        return updated_now, seen_in_guard | guard_before_update

    def stop_condition(_, context: Tuple[Set[str], Set[str]]):
        updated, seen_in_guard = context
        return len(updated | seen_in_guard) == len(uninitialised)

    def key_fn(state, context: Tuple[Set[str], Set[str]]):
        updated, seen_in_guard = context
        return state, frozenset(updated), frozenset(seen_in_guard)

    program_bfs(
        program,
        (set(), set()),
        step,
        stop_condition=stop_condition,
        key_fn=key_fn,
        from_state=init_state,
    )

    return {Variable(name) for name in matters}


def classify_initial_values(
    program, from_state=None
) -> tuple[Set[Variable], Set[Variable]]:
    """Classify uninitialised variables by whether their initial value matters.

    Traverses from the initial state and stops a branch when every uninitialised
    variable has either appeared in a guard or been updated. A variable is
    classified as *relevant* if any guard checks it before the first update on
    some path; otherwise it is *irrelevant* because it is updated before any
    guard dependency.

    Note, further analysis of the LTL objective may be needed to reveal whether
    a relevant variable's initial value can actually influence satisfaction of
    the formula. The analysis here is purely based on the program's transitions.
    """

    relevant = value_dependencies(program, from_state)
    uninitialised = {Variable(v) for v in program.unset_init_vars}
    irrelevant = uninitialised - relevant
    return relevant, irrelevant


def classify_initial_values_with_ltl_horizon(
    program,
    objective_formula: Formula,
    from_state=None,
    *,
    bad_states: Optional[Set[Hashable]] = None,
    ignore_lose_state: bool = True,
) -> tuple[Set[Variable], Set[Variable]]:
    """Classify initial values using guard-flow + conservative temporal horizon checks.

    This keeps the current guard-based classification and refines "irrelevant"
    candidates by tracking whether initial-value influence can survive until a
    potential objective read.

    The temporal side is conservative:
    - `X(phi)` contributes no "read-now" variables.
    - one-step progression is syntactic (`X(phi) -> phi`) and recursive.
    - if a non-empty influence configuration repeats, the variable is treated as
      relevant (unknown horizon / possible infinite influence).

    `bad_states` marks states where the analysis should stop tracking influence:
    once a bad state is reached, later objective occurrences are ignored.
    `ignore_lose_state=True` adds state "lose" to `bad_states` when present.
    """

    relevant, guard_irrelevant = classify_initial_values(program, from_state=from_state)
    if objective_formula is None or len(guard_irrelevant) == 0:
        return relevant, guard_irrelevant

    objective = normalize_ltl(propagate_negations(objective_formula))
    local_var_names = {v.name for v in program.local_vars}

    if len(local_var_names) == 0:
        return relevant, guard_irrelevant

    def _vars_read_now(formula: Formula) -> set[str]:
        if isinstance(formula, UniOp):
            if formula.op == "X":
                return set()
            return _vars_read_now(formula.right)
        if isinstance(formula, BiOp):
            return _vars_read_now(formula.left) | _vars_read_now(formula.right)
        return {str(v) for v in formula.variablesin()}

    def _shift_one(formula: Formula) -> Formula:
        if isinstance(formula, UniOp):
            if formula.op == "X":
                return formula.right
            return UniOp(formula.op, _shift_one(formula.right))
        if isinstance(formula, BiOp):
            return BiOp(_shift_one(formula.left), formula.op, _shift_one(formula.right))
        return formula

    analysis_bad_states: set[str] = set()
    if bad_states is not None:
        analysis_bad_states |= {str(s) for s in bad_states}
    if ignore_lose_state and any(str(s) == "lose" for s in program.states):
        analysis_bad_states.add("lose")

    transitions_by_state: dict[Hashable, list[Transition]] = {
        state: list(program.state_to_trans.get(state, [])) for state in program.states
    }

    guard_vars_by_transition: dict[Transition, set[str]] = {}
    update_deps_by_transition: dict[Transition, dict[str, set[str]]] = {}
    for outgoing in transitions_by_state.values():
        for t in outgoing:
            guard_vars_by_transition[t] = {
                str(v) for v in t.condition.variablesin() if str(v) in local_var_names
            }
            update_deps_by_transition[t] = {
                str(u.left): {
                    str(v) for v in u.right.variablesin() if str(v) in local_var_names
                }
                for u in t.action
                if str(u.left) in local_var_names
            }

    start_state = program.initial_state if from_state is None else from_state

    def _may_matter(seed: Variable) -> bool:
        seed_name = seed.name
        current_formula = objective
        current_configs: set[tuple[Hashable, frozenset[str]]] = {
            (start_state, frozenset({seed_name}))
        }
        seen_pairs: set[tuple[str, frozenset[tuple[Hashable, frozenset[str]]]]] = set()

        while True:
            if len(current_configs) == 0:
                return False

            read_now = _vars_read_now(current_formula) & local_var_names
            if any(len(tainted & read_now) > 0 for _, tainted in current_configs):
                return True

            if all(len(tainted) == 0 for _, tainted in current_configs):
                return False

            pair_key = (
                str(current_formula),
                frozenset(current_configs),
            )
            if pair_key in seen_pairs:
                return False
            seen_pairs.add(pair_key)

            next_configs: set[tuple[Hashable, frozenset[str]]] = set()
            for state, tainted in current_configs:
                if str(state) in analysis_bad_states:
                    continue
                outgoing = transitions_by_state.get(state, [])
                if len(outgoing) == 0:
                    next_configs.add((state, tainted))
                    continue
                for transition in outgoing:
                    if len(guard_vars_by_transition[transition] & tainted) > 0:
                        return True

                    transition_deps = update_deps_by_transition[transition]
                    next_tainted = set()
                    for local_var_name in local_var_names:
                        rhs_vars = transition_deps.get(local_var_name, {local_var_name})
                        if any(v in tainted for v in rhs_vars):
                            next_tainted.add(local_var_name)
                    if str(transition.tgt) in analysis_bad_states:
                        continue
                    next_configs.add((transition.tgt, frozenset(next_tainted)))

            current_configs = next_configs
            current_formula = _shift_one(current_formula)

    temporal_relevant: set[Variable] = set()
    temporal_irrelevant: set[Variable] = set()
    for var in guard_irrelevant:
        if _may_matter(var):
            temporal_relevant.add(var)
        else:
            temporal_irrelevant.add(var)

    return relevant | temporal_relevant, temporal_irrelevant


def reachable_states(program) -> tuple[Set[Hashable], dict[Hashable, Set[Hashable]]]:
    """Return states reachable from the program's initial state."""

    reachable: Set[Hashable] = set()
    reachable_from: dict[Hashable, Set[Hashable]] = {}

    def step(_, __, transition: Transition):
        reachable_from.setdefault(transition.src, set()).add(transition.tgt)
        return None

    def on_visit(state, _):
        reachable.add(state)

    program_bfs(program, None, step, on_visit=on_visit, key_fn=lambda s, _: s)

    # saturate reachable_from
    changed = True
    while changed:
        changed = False
        for src in list(reachable_from.keys()):
            new_targets = set()
            for mid in reachable_from[src]:
                # Terminal states may have no outgoing transitions.
                new_targets.update(reachable_from.get(mid, set()))
            before = len(reachable_from[src])
            reachable_from[src].update(new_targets)
            if len(reachable_from[src]) > before:
                changed = True

    return reachable, reachable_from


def program_sccs(program) -> list[Set[Transition]]:
    """Return SCCs as sets of transitions using a DFS-based two-pass algorithm."""

    states = set(program.states)

    adjacency: dict[Hashable, list[Hashable]] = {state: [] for state in states}
    reverse_adjacency: dict[Hashable, list[Hashable]] = {state: [] for state in states}
    for transition in program.transitions:
        adjacency[transition.src].append(transition.tgt)
        reverse_adjacency[transition.tgt].append(transition.src)

    order: list[Hashable] = []
    program_dfs(
        sorted(states, key=str),
        lambda node: adjacency.get(node, []),
        on_exit=order.append,
    )

    assigned: Set[Hashable] = set()
    sccs: list[Set[Hashable]] = []
    for node in reversed(order):
        if node in assigned:
            continue
        component: Set[Hashable] = set()
        program_dfs(
            [node],
            lambda n: reverse_adjacency.get(n, []),
            on_enter=component.add,
            visited=assigned,
        )
        sccs.append(component)

    transition_sccs: list[Set[Transition]] = []
    for component in sccs:
        trans_in_component = {
            transition
            for transition in program.transitions
            if transition.src in component and transition.tgt in component
        }
        transition_sccs.append(trans_in_component)

    return transition_sccs


def _conjuncts(formula):
    if isinstance(formula, BiOp) and formula.op == BoolBiOps.CONJ:
        return formula.sub_formulas_up_to_associativity()
    return [formula]


def _extract_guard_const_equalities(
    condition, tracked_vars: set[str]
) -> dict[str, Value] | None:
    """Extract var=const facts from a conjunctive guard.

    Returns ``None`` if contradictory equalities are found.
    """

    eqs: dict[str, Value] = {}
    for atom in _conjuncts(condition):
        if not isinstance(atom, BiOp):
            continue
        if atom.op not in (MathRels.EQ, BoolBiOps.IFF):
            continue

        lhs, rhs = atom.left, atom.right
        var = None
        const = None
        if isinstance(lhs, Variable) and isinstance(rhs, Value):
            var, const = lhs, rhs
        elif isinstance(rhs, Variable) and isinstance(lhs, Value):
            var, const = rhs, lhs

        if var is None or var.name not in tracked_vars:
            continue
        if var.name in eqs and eqs[var.name] != const:
            return None
        eqs[var.name] = const
    return eqs


def _merge_must_maps(
    left: dict[str, Value], right: dict[str, Value]
) -> dict[str, Value]:
    return {
        var: value
        for var, value in left.items()
        if var in right and right[var] == value
    }


def _transfer_constants(
    facts_in: dict[str, Value],
    transition: Transition,
    tracked_vars: set[str],
    symbol_table,
) -> dict[str, Value] | None:
    facts = dict(facts_in)

    guard_eqs = _extract_guard_const_equalities(transition.condition, tracked_vars)
    if guard_eqs is None:
        return None
    for var, value in guard_eqs.items():
        if var in facts and facts[var] != value:
            return None
        facts[var] = value

    for action in transition.action:
        lhs = action.left.name
        if lhs not in tracked_vars:
            continue

        subst = {Variable(v): c for v, c in facts.items()}
        rhs = action.right.replace_formulas(subst)
        try:
            rhs = simplify_formula_with_math_wo_type_constraints(rhs, symbol_table)
        except Exception:
            pass

        if isinstance(rhs, Value):
            facts[lhs] = rhs
            continue
        if isinstance(rhs, Variable) and rhs.name in facts:
            facts[lhs] = facts[rhs.name]
            continue

        facts.pop(lhs, None)

    return facts


def location_constant_invariants(program) -> dict[Hashable, dict[str, Value]]:
    """Compute per-location must-hold constant facts ``var = c``.

    Facts are propagated forward from the initial state and merged with set
    intersection at joins (must-analysis).
    """

    tracked_vars = {v.name for v in getattr(program, "local_vars", [])}
    if not tracked_vars:
        return {}

    by_src: dict[Hashable, list[Transition]] = defaultdict(list)
    for transition in program.transitions:
        by_src[transition.src].append(transition)

    init_facts = {
        var: value
        for var, value in getattr(program, "init_var_values", {}).items()
        if var in tracked_vars and isinstance(value, Value)
    }

    in_facts: dict[Hashable, dict[str, Value]] = {program.initial_state: init_facts}
    queue = deque([program.initial_state])

    while queue:
        state = queue.popleft()
        state_facts = in_facts.get(state, {})
        for transition in by_src.get(state, []):
            out_facts = _transfer_constants(
                state_facts,
                transition,
                tracked_vars,
                program.symbol_table,
            )
            if out_facts is None:
                continue

            tgt = transition.tgt
            prev = in_facts.get(tgt)
            if prev is None:
                in_facts[tgt] = out_facts
                queue.append(tgt)
                continue

            merged = _merge_must_maps(prev, out_facts)
            if merged != prev:
                in_facts[tgt] = merged
                queue.append(tgt)

    return in_facts


def simplify_with_location_constants(program) -> tuple[int, int]:
    """Substitute per-location constants into transition guards/updates.

    Returns ``(simplified, removed_unsat)`` counts.
    """

    invariants = location_constant_invariants(program)
    if not invariants:
        return 0, 0

    simplified = 0
    removed_unsat = 0
    new_transitions = []

    for transition in program.transitions:
        facts = invariants.get(transition.src, {})
        if not facts:
            new_transitions.append(transition)
            continue

        subst = {Variable(v): c for v, c in facts.items()}

        new_condition = transition.condition.replace_formulas(subst)
        try:
            new_condition = simplify_formula_with_math_wo_type_constraints(
                new_condition,
                program.symbol_table,
            )
        except Exception:
            pass

        if not sat(new_condition, program.symbol_table):
            removed_unsat += 1
            continue

        changed = new_condition != transition.condition
        new_actions = []
        for action in transition.action:
            new_rhs = action.right.replace_formulas(subst)
            try:
                new_rhs = simplify_formula_with_math_wo_type_constraints(
                    new_rhs,
                    program.symbol_table,
                )
            except Exception:
                pass
            if new_rhs != action.right:
                changed = True
            new_actions.append(Update(action.left, new_rhs))

        if changed:
            simplified += 1
            new_transition = Transition(
                transition.src,
                new_condition,
                new_actions,
                transition.output,
                transition.tgt,
            )
            new_transition.pred_upgrades = list(transition.pred_upgrades)
            new_transitions.append(new_transition)
        else:
            new_transitions.append(transition)

    if simplified > 0 or removed_unsat > 0:
        program.transitions = new_transitions

    return simplified, removed_unsat
