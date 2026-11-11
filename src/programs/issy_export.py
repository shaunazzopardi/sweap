"""Serialize sweap problems using the Issy v3.0 high-level format."""

from __future__ import annotations

from collections import defaultdict
import re
from typing import TYPE_CHECKING

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, Number, Type
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import normalize_ltl, type_constraint
from prop_lang.value import Value
from prop_lang.variable import Variable

if TYPE_CHECKING:
    from programs.program import Program
    from programs.transition import Transition


RELATIONS = {"=", "!=", "<", ">", "<=", ">="}
LOGICAL_OPERATORS = {"&", "|", "->", "<->", "U", "W", "R"}
RESERVED_NAMES = {
    "assume", "assert", "input", "state", "loc", "from", "to", "with",
    "game", "formula", "int", "bool", "real", "def", "F", "X", "G", "U",
    "W", "R", "Safety", "Reachability", "Buechi", "CoBuechi", "ParityMaxOdd",
    "keep", "havoc", "true", "false", "abs", "mod",
}


def issy_names(names: set[str]) -> dict[str, str]:
    """Preserve legal names and deterministically rename others without collisions."""
    legal = {
        name for name in names
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name)
        and name not in RESERVED_NAMES
    }
    result = {name: name for name in legal}
    used = set(legal)
    for name in sorted(names - legal):
        base = "sweap" + name.encode("utf-8").hex()
        candidate = base
        suffix = 0
        while candidate in used:
            suffix += 1
            candidate = f"{base}x{suffix}"
        result[name] = candidate
        used.add(candidate)
    return result


def restore_next_predicates(
    formula: Formula, declared_names: set[str], controller_props: set[str],
    input_props: set[str] | None = None,
) -> Formula:
    """Reverse imported X(prev_rep(predicate)) without introducing history state.

    Only undeclared *_prev aliases of declared variables are treated as history.
    X commutes with the Boolean and future temporal operators, so a whole shifted
    expression can be restored, including the guards inserted around minigames.
    """
    previous = {
        str(variable): str(variable)[:-5]
        for variable in formula.variablesin()
        if str(variable).endswith("_prev")
        and str(variable) not in declared_names
        and str(variable)[:-5] in declared_names
    }
    if not previous:
        return formula
    event_props = controller_props | (input_props or set())

    def has_previous(expr: Formula) -> bool:
        return any(str(variable) in previous for variable in expr.variablesin())

    def shift(expr: Formula) -> Formula:
        if not has_previous(expr):
            return UniOp("X", expr)
        variables = list(expr.variablesin())
        # Controllers are already printed as next values; inputs cannot be primed.
        # Existing primes also need an X rather than an unsupported double prime.
        if not any(
            variable.is_next() or str(variable) in event_props
            for variable in variables
        ):
            return expr.replace_vars({
                variable: Variable(previous.get(str(variable), str(variable) + "'"))
                for variable in variables
            })
        if isinstance(expr, BiOp) and str(expr.op) in LOGICAL_OPERATORS:
            return BiOp(shift(expr.left), expr.op, shift(expr.right))
        if isinstance(expr, UniOp) and str(expr.op) in {"!", "X", "G", "F"}:
            return UniOp(expr.op, shift(expr.right))
        return UniOp("X", expr)

    def restore(expr: Formula) -> Formula:
        if isinstance(expr, UniOp):
            right = restore(expr.right)
            if str(expr.op) == "X" and has_previous(right):
                return shift(right)
            return UniOp(expr.op, right)
        if isinstance(expr, BiOp):
            return BiOp(restore(expr.left), expr.op, restore(expr.right))
        if isinstance(expr, MathExpr):
            return MathExpr(restore(expr.formula))
        return expr

    return restore(formula)


class IssyPrinter:
    def __init__(
        self, symbol_table: dict[str, Type], names: dict[str, str] | None = None,
        *, logical_constants: bool = False,
        controller_props: set[str] | None = None,
    ):
        self.symbol_table = symbol_table
        self.logical_constants = logical_constants
        self.controller_props = frozenset(controller_props or ())
        self.names = names if names is not None else issy_names(
            {name.rstrip("'") for name in symbol_table}
        )

    def name(self, name: str) -> str:
        base = str(name).rstrip("'")
        primes = str(name)[len(base):]
        return self.names.get(base, base) + primes

    def reference(self, variable: Variable) -> str:
        """Controller propositions denote this transition's chosen next value."""
        name = str(variable)
        if name in self.controller_props:
            name += "'"
        return self.name(name)

    def nondeterministic_value(self, variable: Variable) -> str:
        """Leave the value free within its Sweap type's domain."""
        base = Variable(str(variable).rstrip("'"))
        domain = type_constraint(base, self.symbol_table)
        return self.formula(domain.replace_vars({base: variable}))

    def boolean_equivalence(self, left: Formula, right: Formula) -> str:
        """Avoid Issy v3's incorrect compilation of iff (as of issy commit 980c9e8)."""
        for constant, other in ((right, left), (left, right)):
            if isinstance(constant, Value):
                if constant.is_true():
                    return self.formula(other)
                if constant.is_false():
                    text = self.formula(other)
                    return f"!{text}" if isinstance(other, Variable) else f"!({text})"
        lhs, rhs = self.formula(left), self.formula(right)
        return f"(({lhs} && {rhs}) || (!({lhs}) && !({rhs})))"

    def is_boolean(self, expr: Formula) -> bool:
        if isinstance(expr, Variable):
            return self.symbol_table.get(str(expr).rstrip("'")) == BOOLEAN
        if isinstance(expr, Value):
            return expr.is_true() or expr.is_false()
        if isinstance(expr, MathExpr):
            return self.is_boolean(expr.formula)
        if isinstance(expr, BiOp):
            return str(expr.op) in LOGICAL_OPERATORS | RELATIONS
        return isinstance(expr, UniOp) and str(expr.op) != "-"

    def term(self, expr: Formula) -> str:
        """Print an arithmetic term, without predicate brackets."""
        if isinstance(expr, MathExpr):
            return self.term(expr.formula)
        if isinstance(expr, Variable) and not self.is_boolean(expr):
            return self.reference(expr)
        if isinstance(expr, Value) and not self.is_boolean(expr):
            return str(expr)
        if isinstance(expr, UniOp) and str(expr.op) == "-":
            return f"({expr.op} {self.term(expr.right)})"
        if isinstance(expr, BiOp) and str(expr.op) in {
            "+", "-", "*"
        }:
            return f"({self.term(expr.left)} {str(expr.op)} {self.term(expr.right)})"
        raise ValueError(f"Unsupported Issy arithmetic term: {expr}")

    def formula(self, expr: Formula) -> str:
        if isinstance(expr, MathExpr):
            return self.formula(expr.formula)
        if isinstance(expr, Value):
            if expr.is_true():
                # Issy v3 fails to wrap bare constants as LLissy temporal atoms.
                return "[0 = 0]" if self.logical_constants else "true"
            if expr.is_false():
                return "[0 = 1]" if self.logical_constants else "false"
        if isinstance(expr, Variable):
            return f"[{self.reference(expr)}]"
        if isinstance(expr, Update):
            if isinstance(expr.right, NonDeterministic):
                return self.nondeterministic_value(Variable(f"{expr.left}'"))
            return self.formula(BiOp(Variable(f"{expr.left}'"), "=", expr.right))
        if isinstance(expr, UniOp) and str(expr.op) in {"!", "X", "G", "F"}:
            return f"{expr.op}({self.formula(expr.right)})"
        if isinstance(expr, BiOp):
            op = str(expr.op)
            if op in LOGICAL_OPERATORS:
                if op == "<->":
                    return self.boolean_equivalence(expr.left, expr.right)
                op = {"&": "&&", "|": "||"}.get(op, op)
                return f"({self.formula(expr.left)} {op} {self.formula(expr.right)})"
            if op in RELATIONS:
                if op in {"=", "!="} and (
                    self.is_boolean(expr.left) or self.is_boolean(expr.right)
                ):
                    equality = self.boolean_equivalence(expr.left, expr.right)
                else:
                    relation = "=" if op == "!=" else op
                    equality = f"[{self.term(expr.left)} {relation} {self.term(expr.right)}]"
                return f"!({equality})" if op == "!=" else equality
        raise ValueError(f"Unsupported Issy formula: {expr}")


def transition_body(
    transition: Transition, printer: IssyPrinter, states_in_spec: set[str]
) -> str:
    """Keep each guard together with its updates when combining parallel edges."""
    parts = [printer.formula(transition.condition)]
    stutters = sorted(
        printer.name(str(u.left))
        for u in transition.action if u.left == u.right
    )
    if stutters:
        parts.append(f"keep({' '.join(stutters)})")
    parts.extend(
        printer.formula(u)
        for u in sorted(transition.action, key=lambda u: str(u.left))
        if u.left != u.right
    )
    for state in sorted(states_in_spec):
        atom = f"[{printer.name(state)}']"
        parts.append(atom if state == transition.tgt else f"!{atom}")
    return "(" + " && ".join(parts) + ")"


def program_to_issy(program: Program, spec: Formula) -> str:
    """Export ISSY version of sweap problem"""
    constants = getattr(program, "constants", {})
    spec = normalize_ltl(spec.replace_vars(constants))
    controller_props = {str(variable) for variable, _ in program.con_events}
    declared_names = (
        {str(variable) for variable in program.local_vars}
        | {str(variable) for variable, _ in program.env_events}
        | controller_props | set(program.states)
    )
    constant_values = {str(variable): value for variable, value in constants.items()}
    # A projected constant's history has the same value on every relevant step.
    spec = spec.replace_vars({
        variable: constant_values[str(variable)[:-5]]
        for variable in spec.variablesin()
        if str(variable).endswith("_prev")
        and str(variable) not in declared_names
        and str(variable)[:-5] in constant_values
    })
    spec = restore_next_predicates(
        spec, declared_names, controller_props,
        {str(variable) for variable, _ in program.env_events},
    )
    names = issy_names(set(program.symbol_table) | set(program.states))
    printer = IssyPrinter(
        program.symbol_table, names, controller_props=controller_props
    )
    logical_printer = IssyPrinter(
        program.symbol_table, names, logical_constants=True,
        controller_props=controller_props,
    )
    states_in_spec = {
        str(variable).rstrip("'") for variable in spec.variablesin()
    } & set(program.states)

    def issy_type(typ: Type) -> str:
        if typ == BOOLEAN:
            return "bool"
        if isinstance(typ, Number):
            return "int"
        raise ValueError(f"Unsupported type for Issy: {typ}")

    declarations = []
    for role, variables in (
        ("input", program.env_events), ("state", program.con_events)
    ):
        declarations.extend(
            f"{role} {issy_type(t)} {printer.name(str(v))}"
            for v, t in sorted(variables, key=lambda item: str(item[0]))
        )
    declarations.extend(
        f"state {issy_type(program.symbol_table[str(v)])} {printer.name(str(v))}"
        for v in sorted(program.local_vars, key=str)
    )
    declarations.extend(
        f"state bool {printer.name(s)}" for s in sorted(states_in_spec)
    )
    objective = []
    for variable, typ in sorted(program.env_events, key=lambda item: str(item[0])):
        domain = type_constraint(Variable(str(variable)), {str(variable): typ})
        if not (isinstance(domain, Value) and domain.is_true()):
            objective.append(f"assume G({logical_printer.formula(domain)})")
    for state in sorted(states_in_spec):
        negation = "!" if state != program.initial_state else ""
        objective.append(f"assume {negation}[{printer.name(state)}]")
    initial = [
        (
            logical_printer.nondeterministic_value(Variable(str(v)))
            if isinstance(value, NonDeterministic)
            else logical_printer.formula(BiOp(Variable(str(v)), "=", value))
        )
        for v, value in sorted(
            program.init_var_values.items(), key=lambda item: str(item[0])
        )
    ]
    if initial:
        objective.append("assume " + " && ".join(initial))
    objective.append("assert " + logical_printer.formula(spec))

    grouped = defaultdict(list)
    for transition in program.transitions:
        grouped[(transition.src, transition.tgt)].append(
            transition_body(transition, printer, states_in_spec)
        )
    local_domains = []
    for variable in sorted(program.local_vars, key=str):
        domain = type_constraint(Variable(str(variable)), program.symbol_table)
        if not (isinstance(domain, Value) and domain.is_true()):
            local_domains.append(printer.formula(domain))
    # Domains restrict the game validator's state space as well as actual moves.
    location_domain = (
        " with (" + " && ".join(local_domains) + ")" if local_domains else ""
    )
    game = [
        f"loc {printer.name(state)} 1{location_domain}"
        for state in sorted(program.states)
    ]
    game.extend(
        f"from {printer.name(src)} to {printer.name(tgt)} with "
        + " || ".join(sorted(set(bodies)))
        for (src, tgt), bodies in sorted(grouped.items())
    )
    return (
        "formula {\n\t" + "\n\t".join(objective) + "\n}\n\n"
        + "\n".join(declarations) + "\n\n"
        + f"game Safety from {printer.name(program.initial_state)} {{\n\t"
        + "\n\n\t".join(game) + "\n}"
    )
