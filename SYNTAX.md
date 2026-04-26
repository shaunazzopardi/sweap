# `.prog` Syntax

This file gives an overview of how to specify sweap problems in `.prog` syntax, used with the `--p` flag in command line invocation:

```python src/main.py --p <spec.prog>```.

The format describes a symbolic reactive synthesis problem: a finite arena, input/output variables, state variables, transitions, and an LTL
objective.

## Skeleton

A `.prog` file consists of a single arena declaration:

```text
arena <name> {
    CONTROL STATES { <states> }

    INPUTS { <input-events> }

    OUTPUTS { <output-events> }

    STATE VARIABLES { <local-state-variables> }

    TRANSITIONS [<options>] { <transitions> }

    OBJECTIVE { <ltl-objective> }
}
```

The top-level sections may appear in any order. Section names must not be
duplicated. The parser requires control states, inputs, outputs, local state
variables, and transitions. In normal synthesis usage, also provide an
`OBJECTIVE` section.

Preferred section names and accepted aliases (for backwards compatibility) are:

```text
arena            (also accepts program)
CONTROL STATES   (also accepts STATES)
INPUTS           (also accepts ENVIRONMENT EVENTS)
OUTPUTS          (also accepts CONTROLLER EVENTS)
STATE VARIABLES  (also accepts VALUATION)
OBJECTIVE        (also accepts SPECIFICATION)
```

Commas and semicolons are both accepted as separators in declaration lists and
transition lists. A trailing comma or semicolon is accepted.

## Names

Program names and event/state-variable declarations use:

```text
[_a-zA-Z][_a-zA-Z0-9$@_-]*
```

State names are parsed more permissively:

```text
[a-zA-Z0-9@$_-]+
```

Formula atoms are parsed by the LTL parser and are narrower in practice:

```text
_?[a-zA-Z][a-zA-Z0-9_-]*
```

For names that appear in guards or specifications, prefer ordinary
letter-starting identifiers with letters, digits, and underscores. Avoid names
matching reserved internal patterns such as `true`, `false`, `lose`, `pred_*`,
`bin_*`, `guard_*`, `act_*`, `eq_con_*`, `sat_con_*`, and
`minigame_event_*`.

Control-state names, event names, and local state-variable names must be
globally unique.

## Control States

The `CONTROL STATES` section lists control states. Exactly one state must be tagged
`: init`.

```text
CONTROL STATES {
    idle : init, busy, done
}
```

## Variables

Accepted variable types are the following:

```text
bool, boolean
nat, natural
int, integer
[lower..upper], (lower..upper], [lower..upper), (lower..upper)
```

### Input and Output Variables

`INPUTS` and `OUTPUTS` declare variables controlled by the environment and
controller respectively. The older `ENVIRONMENT EVENTS` and `CONTROLLER EVENTS`
section names are still parsed for backwards compatibility, but new files
should use `INPUTS` and `OUTPUTS`.

```text
INPUTS {
    request, delta : integer, limit : [0..10]
}

OUTPUTS {
    grant, finished : boolean
}
```

Untyped variables are interpreted as boolean. 

Output variables must be boolean; non-boolean output variables will result in a parsing error.

Empty `INPUTS` and `OUTPUTS` sections are accepted.

### State Variables

`STATE VARIABLES` declares local state variables owned by the program, for example:

```text
STATE VARIABLES {
    count : natural := 0;
    mode : [0..3] := 0;
    enabled : bool := false;
    unconstrained : integer;
    arbitrary_start : integer := *;
}
```

Initial values are optional, omitting `:= ...` leaves the initial value
unconstrained. When unconstrained, the specification universally quantifies over all possible initial values. That is, a controller must work for all possible unspecified initial values, while a counterstrategy must work for at least one initial valuation.

## Formulas

Guards and normal action conditions are propositional formulas over current
state variables, inputs, and outputs. LIA predicates are also allowed.

Common operators:

```plain
true, false, TRUE, FALSE
!p
p & q      or p && q
p | q      or p || q
p -> q     or p => q
p <-> q    or p <=> q
x = y      or x `== y
x != y
x < y, x <= y, x > y, x >= y
x + y, x - y, -x
```

`OBJECTIVE` formulas additionally allow LTL operators and reference to control states (and also LIA predicates):

```text
X p
F p
G p
p U q
p W q
p R q
p M q
```

Examples:

```text
G(request -> F grant)
G((count >= 0) -> F(done & count = 0))
(!idle) U done
```

## Transitions

Transitions define how the state variables values are allowed to evolve. sweap supports two styles of transition specification: guarded assignments, and propositional formulas over current and next variable labels:

```text
source -> target [ guard $ <guarded-assignments|formula(V,V')> ]
```

The guard is optional and if not present the interpretation defaults to `true`. 

### Canonical Transitions

The high-level syntax, while more concise, is not the canonical arena format used internally by sweap. The canonical arena transitions are simpler, consisting of a source state, target state, a guard formula over current variables only, and explicit assignments for each local state variables. 

In a canonical arena, given a set of transitions from a state `s`, with guards `g_0`, ..., `g_n`, these guards must be mutually exclusive, and they must cover all possible valuations of the variables in `s` (i.e. `g_0 | ... | g_n` must be a tautology). 

Non-mutually exclusive guards introduce nondeterminism, and will result in a parsing error. A user can manually deal with this non-determinism by introducing new input or output variables to allow the environment or controller to choose between the transitions.

For convenience, sweap allows incomplete guards, but the user must specify how to complete them with the `completion` option (see below). 

To view the canonical arena from a higher-level sweap specification, use the following command:

```text
python src/main.py --p <spec.prog> --translate prog
```

### Guarded Assignments

Assignments are exact updates of a state variable:

```text
x := x + 1
enabled := request & x > 0
```

The left-hand side of an assignment must be a local state variable. The right-hand side is a formula over current input, output, and/or state variables; it cannot reference next variables. For boolean variables, it is any boolean formula over the mentioned variables (including LIA predicates). For integer variables, the right-hand side must be an arithmetic expression over the mentioned variables, using addition, subtraction, and negation.

Assignments are optional. When an assignment for a state variable is not defined, the interpretation defaults to the identity assignment. For a list of assignments, a variable can only be assigned once.

Examples:

```text
idle -> busy [request]
busy -> idle [done $ count := count - 1]
busy -> busy [$ count := count + 1]
busy -> idle [done $]
```

Multiple updates may be separated by commas or semicolons:

```text
q0 -> q1 [request $ count := count + 1; enabled := true]
```

An update can have its own condition using the literal token ` if `:

```text
q -> q [true $
    x := x + 1 if inc;
    x := x - 1 if dec & x > 0;
    active := inc | dec
]
```

For multiple guarded updates to the same variable, the parser treats them in
order: later updates only apply where earlier guards for that same variable did
not apply. If none applies, the variable is left unchanged by normal action
completion.

### `otherwise` Transitions

The special guard `otherwise` is a fallback for one source state:

```text
s0 -> s1 [x > 0 $ x := x - 1],
s0 -> s2 [otherwise $ x := x + 1]
```

It is expanded to the negation of the disjunction of the other guards from the same source state.
At most one `otherwise` transition is allowed per source state.

### Formulas over Current and Next Variables

`#` introduces a relational action formula over current variable values and next state variable values. Use a
prime suffix to refer to the next value of a local variable.

Example transitions:

```text
q0 -> q1 [x <= 0 # (x' = x + 1) & (y' = x)]
q0 -> q1 [x > 0 # (x' = 0) | (x' = 1)]
```

These propositional formulas may reference local state variables (either current
or primed next values), and input and output variables (only current value).

When such a formula does not constrain a local variable, that
variable is treated as **nondeterministically updated, not as an identity update**. Note this differs from the guarded assignment style, where unconstrained variables are treated as identity updates. This allows more concise specification of general relational constraints over next variables, but also requires care to avoid unintentionally leaving variables unconstrained.

An empty `#` therefore allows any next local state for all local variables.

Equality constraints such as `x' = x + 1` are lowered to ordinary updates.
Branching formulas may lower to several transitions. More general relational
constraints over next variables can introduce fresh internal (minigame) states, to allow the controller to choose any value of a next variable that satisfies the constraint. Thus, a transition that appears to take one time step in the original specification may take several time steps in the canonical arena. The LTL objective is modified automatically to ignore these extra time steps, maintaining equirealisability of the original specification.

Example:

```text
q0 -> q1 [true # (x' >= x + 1)]
```

results in the addition of a fresh internal state `q0_minigame_0`, a fresh controller output `minigame_event_0`, and the following transitions:

```text
q0 -> q0_minigame_0 [true $ x := x + 1],
q0_minigame_0 -> q0_minigame_0 [!minigame_event_0 $ x := x + 1],
q0_minigame_0 -> q1 [minigame_event_0],
```

If the objective was `F (x = 10)`, it would be automatically modified to `F (!q0_minigame_0 & x = 10) & G(F(!q0_minigame_0))`.

## Transition Options

Options are written after `TRANSITIONS`:

```text
TRANSITIONS [completion=stutter] { ... }
TRANSITIONS [completion=lose] { ... }
```

These two options are the only currently supported options. They specify how to complete the transition relation when the guards do not cover all possible valuations of the variables.

`completion=stutter` fills uncovered behavior from a reachable source state with stutter transitions (remain in same control state, and state variables maintain their current value in the next state).

`completion=lose` fills uncovered behavior with transitions to a generated
`lose` sink state and adds `G(!lose)` to the objective guarantees. Reaching this state, if the environment respects the assumptions, results in a loss for the controller.

If no `completion` option is specified, incomplete transition coverage results in an error.

## Complete Example

```text
program small_counter {
    CONTROL STATES {
        idle : init, busy
    }

    INPUTS {
        request, reset
    }

    OUTPUTS {
        grant
    }

    STATE VARIABLES {
        count : natural := 0;
        served : bool := false;
    }

    TRANSITIONS [completion=stutter] {
        idle -> busy [request $ count := count + 1; served := false],
        busy -> idle [grant & count > 0 $ count := count - 1; served := true],
    }

    OBJECTIVE {
        G(request -> F grant)
    }
}
```

The canonical arena for this example will add the following transitions:

```text
idle -> idle [!request]
busy -> busy [!grant | count = 0]

## Guarded-Update Example

```text
program robot_step {
    CONTROL STATES {
        q : init
    }

    INPUTS {
        inc, dec
    }

    OUTPUTS {
        move
    }

    STATE VARIABLES {
        x : integer := 0
    }

    TRANSITIONS [completion=stutter] {
        q -> q [true $
            x := x + 1 if move & inc;
            x := x - 1 if move & dec & x > 0
        ]
    }

    OBJECTIVE {
        G(move -> F(x = 0))
    }
}
```

The canonical arena for this example will have following transition section:

```text
q -> q [move & inc $ x := x + 1],
q -> q [move & dec & x > 0 $ x := x - 1],
q -> q [!((move & inc) | (move & dec & x > 0)) $]
```

## Relational `#` Example

```text
program relational_step {
    CONTROL STATES {
        q0 : init, q1
    }

    INPUTS {
    }

    OUTPUTS {
    }

    STATE VARIABLES {
        x : integer := 0;
        y : integer := 0;
    }

    TRANSITIONS [completion=stutter] {
        q0 -> q1 [true # (x' > x + 1) & (y' = x)],
        q1 -> q1 [true # (x' < x) & (y' = y)]
    }

    OBJECTIVE {
        G true
    }
}
```

The canonical arena for this example will have the following transition section:

```text
q0 -> q0_minigame_0 [true $ x := x + 2, y := x],
q0_minigame_0 -> q0_minigame_0 [!minigame_event_0 $ x := x + 1, y := x],
q0_minigame_0 -> q1 [minigame_event_0],
q1 -> q1_minigame_1 [true $ x := x - 1, y := x],
q1_minigame_0 -> q1_minigame_0 [!minigame_event_0 $ x := x - 1, y := y],
q1_minigame_0 -> q1 [minigame_event_0]
```

Note, if the controller has boolean outputs, we re-use these outputs as the minigame events, so the translation of `#` formulas may not always introduce fresh outputs. Given we massage the LTL objective to ignore behaviour at minigame state equirealisability is preserved, while avoiding introducing unnecessary fresh controller outputs (which would increase the complexity of synthesis).