# This modules implements data-flow analyses for programs

from collections import deque
from typing import Any, Callable, Hashable, Optional, Set, Tuple

from programs.transition import Transition
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


def reachable_states(program) -> Set[Hashable]:
    """Return states reachable from the program's initial state."""

    reachable: Set[Hashable] = set()

    def step(_, __, transition: Transition):
        return None

    def on_visit(state, _):
        reachable.add(state)

    program_bfs(program, None, step, on_visit=on_visit, key_fn=lambda s, _: s)
    return reachable


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
