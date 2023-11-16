from collections import Counter, defaultdict, deque
from copy import deepcopy
from dataclasses import dataclass
from itertools import chain, combinations
from operator import add, mul, sub
from textwrap import dedent

from pysmt.shortcuts import (FALSE, GE, GT, LE, LT, And, Bool, EqualsOrIff,
                             Implies, Int, Not, NotEquals, Or, Symbol,
                             get_free_variables, simplify, substitute)
from pysmt.typing import BOOL, INT
from tatsu.walkers import NodeWalker

from parsing.dsl.parsing import (Assign, BaseNode, Comparison, Decl, Decrement,
                                 If, Increment, Literal, Load, MethodDef)
from parsing.dsl.parsing import Program as ProgramDSL
from parsing.dsl.parsing import (Store, Token, UnaryOp, parse_dsl,
                                 remove_all_versions, remove_version,
                                 to_formula)
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set
from prop_lang.variable import Variable


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


@dataclass
class SymbolTableEntry:
    name: str
    context: 'SymbolTable'
    init: any
    type_: any      # SMT type of the variable
    ast: Decl


class SymbolTable:
    GLOBAL_CTX = "<global>"

    def __init__(self, name=GLOBAL_CTX, parent=None, is_params=False):
        self.name = name
        self.parent = parent
        self.children = []
        self.symbols = {}
        self.is_params = is_params

    def __getitem__(self, key):
        return self.symbols[key]

    def __contains__(self, key):
        return key in self.symbols

    def __str__(self) -> str:
        return f"{self.name}:{self.symbols}"

    def __iter__(self):
        yield from self.symbols.values()
        for child in self.children:
            yield from child

    def add_child(self, name, is_params=False):
        name = name + "##params" if is_params else name
        table = SymbolTable(name, parent=self, is_params=is_params)
        self.children.append(table)
        return table

    def is_local(self):
        return self.parent is not None and not self.is_params

    def lookup(self, name, trail=None) -> SymbolTableEntry:
        if name in self.symbols:
            return self.symbols[name]
        elif self.parent is None:
            trail = trail or []
            trail.append(self)
            trail_fmt = "\n".join(f"{st}" for st in trail)
            raise KeyError(f"Symbol {name} not found in {trail_fmt}")
        else:
            trail = trail or []
            trail.append(self)
            return self.parent.lookup(name, trail)

    def add(self, node: Decl, init) -> SymbolTableEntry:
        builtin_types = {'int': INT, 'bool': BOOL}
        symbol = SymbolTableEntry(
            node.var_name, self, init, builtin_types[node.var_type], node)
        self.symbols[node.var_name] = symbol
        return symbol


class VarRenamer(NodeWalker):
    """Renames every variable to its fully qualified version"""

    GLOBAL_PREFIX = "global"

    def __init__(self):
        super().__init__()
        self.prefix = self.GLOBAL_PREFIX
        self.seen = set()

    def global_name(self, name):
        return f"_{self.GLOBAL_PREFIX}_{name}"

    def prefixed_name(self, name):
        return f"_{self.prefix}_{name}"

    def lookup(self, name):
        if self.prefixed_name(name) in self.seen:
            return self.prefixed_name(name)
        if self.global_name(name) in self.seen:
            return self.global_name(name)
        return name

    def walk_BaseNode(self, node: BaseNode):
        """Default action: just recurse on all children"""
        if node._children:
            for child in node._children:
                self.walk(child)

    def walk_Decl(self, node: Decl):
        name = self.prefixed_name(node.var_name)
        node.var_name = name
        self.seen.add(name)

    def walk_Program(self, node: ProgramDSL):
        self.walk(node.decls)
        self.walk(node.methods)
        self.walk(node.guarantees)

    def walk_Load(self, node: Load):
        node.name = self.lookup(node.name)

    def walk_Store(self, node: Store):
        node.name = self.lookup(node.name)

    def walk_MethodDef(self, node: MethodDef):
        self.prefix = node.name
        self.walk(node.params)
        self.walk(node.body)
        self.walk(node.asserts)
        self.walk(node.assumes)
        self.prefix = self.GLOBAL_PREFIX


class ForkingPath:
    def __init__(self, parent=None, table=None) -> None:
        self.variables = {}
        self.counters = Counter() if parent is None else deepcopy(parent.counters)  # noqa: E501
        self.assignments = {}
        self.conditions = []
        self.children = []
        self.table = table or (SymbolTable() if parent is None else parent.table)  # noqa: E501
        self.parent = parent

    def _lookup(self, name):
        if name in self.variables:
            return self.variables[name]
        return None if self.parent is None else self.parent._lookup(name)

    def fresh(self, name):
        symbol = self.table.lookup(name)
        self.variables[name] = Symbol(f"{name}#{self.counters[name]}", symbol.type_)  # noqa: E501
        self.counters[name] += 1
        return self.variables[name]

    def lookup_or_fresh(self, name):
        return self._lookup(name) or self.fresh(name)

    def add_child(self, table=None):
        child = ForkingPath(self, table)
        self.children.append(child)
        return child

    def get_root(self):
        return self if self.parent is None else self.parent.get_root()

    def leaves(self, start_from=None):
        def descend(n):
            if not n.children:
                yield n
            else:
                for child in n.children:
                    yield from descend(child)
        yield from descend(start_from or self)

    def get_path(self):
        n = self
        conds, asgns = [], {}
        while n is not None:
            conds.extend(n.conditions)
            asgns.update(n.assignments)
            n = n.parent
        return conds, asgns

    def to_transitions(self):
        table = self.table
        conds, asgns = self.get_path()
        subs = []
        local_inits = {}
        for x in asgns:
            name, version = str(x)[1:-1].split("#")
            version = int(version)
            if 0 < version < self.counters[name] - 1:
                # This is neither the 1st or last version of x
                subs.append(x)
            else:
                # Always add x if it is local (= not global nor parameter)
                symb: SymbolTableEntry = table.lookup(name)
                if symb.context.is_local():
                    subs.append(x)
                    # Add information about initial value of x
                    if version == 0:
                        local_inits[x] = symb.init
        asgns.update(local_inits)

        # We topologically sort variables so that we
        # can do the substitution in a single pass
        topo_sort = []
        unsorted = deque(subs)
        while unsorted:
            var = unsorted.popleft()
            if any(var in get_free_variables(asgns[x]) for x in unsorted):
                unsorted.append(var)
            else:
                topo_sort.append(var)

        # Substitute and remove intermediate variables
        for x in topo_sort:
            sub = {x: asgns[x]}
            for y in asgns:
                asgns[y] = substitute(asgns[y], sub)
            conds = [
                substitute(f, {x: asgns[x]})
                for f in conds]
        for x in subs:
            del asgns[x]

        conds = [remove_all_versions(f) for f in conds]
        action = {
            remove_version(x): remove_all_versions(asgns[x])
            for x in asgns}

        # Branch on output variables and yield
        output_vars = {
            x: action[x] for x in action
            if table.lookup(x.symbol_name()).ast.io == "output"}

        actions_wo_out = {x: action[x] for x in action if x not in output_vars}

        for positive_out in powerset(output_vars):
            negated_out = {x for x in output_vars if x not in positive_out}
            new_conds = [c for c in conds]
            new_conds.extend(action[o] for o in positive_out)
            new_conds.extend(Not(action[o]) for o in negated_out)
            yield new_conds, actions_wo_out, positive_out

    def prune(self):
        for x in self.leaves(self.get_root()):
            conds, _ = x.get_path()
            if simplify(And(conds)) == FALSE():
                # print(f"{conds} is unsat, pruning {x} away")
                x.parent.children.remove(x)

    def pprint(self) -> str:
        conds, asgns = self.get_path()
        return f"{conds}-->{asgns}"


class SymexWalker(NodeWalker):

    def __init__(self):
        super().__init__()
        self.paths = {}
        self.fp = ForkingPath()

        self.extern_assumes = {}
        self.extern_asserts = {}
        self.intern_assumes = {}
        self.intern_asserts = {}

        self.extern_triples = defaultdict(list)
        self.intern_triples = defaultdict(list)

    def walk_Decl(self, node: Decl):
        init = self.walk(node.init)
        self.fp.table.add(node, init)
        if self.fp.table.parent is not None and node.init is not None:
            var = self.fp.fresh(node.var_name)
            self.fp.assignments[var] = init

    def walk_Program(self, node: ProgramDSL):
        self.walk(node.decls)
        self.walk(node.methods)

        self.env_choices = {
            name: Symbol(f"_METHOD_{name}") for name in self.extern_triples}
        self.con_choices = {
            name: Symbol(f"_METHOD_{name}") for name in self.intern_triples}

        # Post-processing: add booleans to represent chosen methods
        def add_choice_booleans(triples_dict, booleans_dict):
            for name, triples in triples_dict.items():
                for x in triples:
                    x[0].extend(self.one_hot(name, booleans_dict))
        add_choice_booleans(self.extern_triples, self.env_choices)
        add_choice_booleans(self.intern_triples, self.con_choices)

    def one_hot(self, name, booleans_dict):
        result = [Not(var) if var_name != name else var
                  for var_name, var in booleans_dict.items()]
        return result

    def walk_Load(self, node: Load):
        return self.fp.lookup_or_fresh(node.name)

    def walk_BinOp(self, node: Comparison):
        op = {
            Token.EQ: EqualsOrIff, Token.NE: NotEquals,
            Token.GE: GE, Token.GT: GT, Token.LE: LE, Token.LT: LT,
            Token.AND: And, Token.OR: Or, Token.IMPL: Implies,
            Token.MUL: mul, Token.ADD: add, Token.SUB: sub}
        left = self.walk(node.left)
        right = self.walk(node.right)
        return op[node.op](left, right)

    def walk_UnaryOp(self, node: UnaryOp):
        op = {Token.NOT: Not}
        expr = self.walk(node.expr)
        return op[node.op](expr)

    def walk_Literal(self, node: Literal):
        return (
            Bool(node.value)
            if isinstance(node.value, bool)
            else Int(node.value))

    def walk_Store(self, node: Store):
        return self.fp.fresh(node.name)

    def walk_Assign(self, node: Assign):
        rhs = self.walk(node.rhs)
        lhs = self.walk(node.lhs)
        for leaf in self.fp.leaves():
            leaf.assignments[lhs] = rhs

    def _walk_Increment_or_Decrement(self, node, op):
        rhs = self.fp.lookup_or_fresh(node.var_name.name)
        lhs = self.walk(node.var_name)
        for leaf in self.fp.leaves():
            leaf.assignments[lhs] = op(rhs)

    def walk_Increment(self, node: Increment):
        self._walk_Increment_or_Decrement(node, lambda x: x + 1)

    def walk_Decrement(self, node: Decrement):
        self._walk_Increment_or_Decrement(node, lambda x: x - 1)

    def walk_If(self, node: If):
        or_else = node.or_else or []
        parent_fp = self.fp
        for leaf in self.fp.leaves():
            self.fp = leaf.add_child()
            cond = self.walk(node.cond)
            self.fp.conditions.append(cond)
            self.walk(node.body)

            self.fp = leaf.add_child()
            self.fp.conditions.append(Not(cond))
            self.walk(or_else)
        self.fp = parent_fp

    def walk_MethodDef(self, node: MethodDef):
        self.fp = self.fp.add_child(
            self.fp.table.add_child(node.name, is_params=node.params))
        if node.params:
            self.walk(node.params)
        assumes = [self.walk(n) for n in node.assumes or []]
        asserts = [self.walk(n) for n in node.asserts or []]

        if node.kind == "intern":
            self.intern_asserts[node.name] = [remove_all_versions(x) for x in asserts]  # noqa: E501
            self.intern_assumes[node.name] = [remove_all_versions(x) for x in assumes]  # noqa: E501
        else:
            self.extern_asserts[node.name] = [remove_all_versions(x) for x in asserts]  # noqa: E501
            self.extern_assumes[node.name] = [remove_all_versions(x) for x in assumes]  # noqa: E501

        self.fp.conditions.extend(assumes)
        self.fp.conditions.extend(asserts)

        if node.params:
            self.fp.table = self.fp.table.add_child(node.name)

        self.walk(node.decls)
        self.walk(node.body)

        self.paths[node.name] = self.fp
        while self.fp.parent is not None:
            self.fp = self.fp.parent

        # self.fp.prune()
        for x in self.paths[node.name].leaves():
            if node.kind == "extern":
                self.extern_triples[node.name].extend(x.to_transitions())
            else:
                self.intern_triples[node.name].extend(x.to_transitions())


def dsl_to_program(file_name: str, code: str) -> (Program, list):
    """Parse a DSL program and return a Program"""

    tree = parse_dsl(code)
    renamer = VarRenamer()
    renamer.walk(tree)
    symex_walker = SymexWalker()
    symex_walker.walk(tree)
    table = symex_walker.fp.get_root().table

    # All method parameters are treated as events
    events = {
        kind: [
            Variable(s.name) for s in table
            if s.context.is_params and s.ast.parent.kind == kind]
        for kind in ("extern", "intern")}
    events["extern"].extend([Variable(s.symbol_name()) for s in symex_walker.env_choices.values()])  # noqa: E501
    events["intern"].extend([Variable(s.symbol_name()) for s in symex_walker.con_choices.values()])  # noqa: E501

    out_cw, out_cl = Variable("_con_wins"), Variable("_con_loses")
    out_actions = [
        Variable(s.name) for s in table.symbols.values()
        if s.ast.io == "output"]
    out_actions.extend((out_cw, out_cl))
    init_values = [
        TypedValuation(s.name, str(s.type_).lower(), to_formula(s.init))
        for s in table.symbols.values()
        if s.ast.io != "output"]

    def _conjunct_smt(cond):
        return conjunct_formula_set(to_formula(c) for c in cond)

    def _disjunct_smt(cond):
        return disjunct_formula_set(to_formula(c) for c in cond)

    def triples_to_transitions(s0, triples_dict: dict):

        def _act_to_formula(act: dict):
            return [
                BiOp(to_formula(lhs), "=", to_formula(rhs))
                for lhs, rhs in act.items()]

        def _variables(out):
            return [Variable(x.symbol_name()) for x in out]

        transitions = [
            Transition(s0, _conjunct_smt(cond), _act_to_formula(act), _variables(out), s0)  # noqa: E501
            for method_triples in triples_dict.values()
            for (cond, act, out) in method_triples]
        return transitions

    s0, s_con_wins, s_con_loses = 's0', 's_con_wins', 's_con_loses'

    env_ts = triples_to_transitions(s0, symex_walker.extern_triples)
    con_ts = triples_to_transitions(s0, symex_walker.intern_triples)

    env_ts.append(Transition(s_con_wins, None, [], [out_cw], s_con_wins))
    env_ts.append(Transition(s_con_loses, None, [], [out_cl], s_con_loses))

    # Go to losing/winning state if any assertion/assumption is violated
    def add_assert_violations(choices, asserts, assumes, ts, sink):
        for method in choices:
            if method in asserts:
                assertion = Or(Not(x) for x in asserts[method])
                if method in assumes:
                    assertion = And(assertion, *assumes[method])
                ind = symex_walker.one_hot(method, choices)
                ind.append(assertion)
                assertion = And(ind)
                assertion = to_formula(assertion)
                out = out_cl if sink == s_con_loses else out_cw
                ts.append(Transition(s0, assertion, [], [out], sink))

    # Environment cannot violate an assume() to break an assert()
    add_assert_violations(symex_walker.env_choices, symex_walker.extern_asserts, symex_walker.extern_assumes, env_ts, s_con_loses)  # noqa: E501
    # Controller cannot violate an assert() to break an assume()
    add_assert_violations(symex_walker.con_choices, symex_walker.intern_assumes, symex_walker.intern_asserts, con_ts, s_con_wins)  # noqa: E501

    add_assert_violations(symex_walker.con_choices, symex_walker.intern_asserts, {}, con_ts, s_con_loses)  # noqa: E501
    add_assert_violations(symex_walker.env_choices, symex_walker.extern_assumes, {}, env_ts, s_con_wins)  # noqa: E501

    # Guarantee at most one method is chosen
    def add_mutex_guarantee(choices, ts, sink):
        if len(choices) > 1:
            dnf = (And(x, y) for x, y in combinations(choices.values(), 2))
            out = out_cl if sink == s_con_loses else out_cw
            ts.append(Transition(s0, _disjunct_smt(dnf), [], [out], sink))

    add_mutex_guarantee(symex_walker.env_choices, env_ts, s_con_wins)
    add_mutex_guarantee(symex_walker.con_choices, con_ts, s_con_loses)

    # Prevent stuttering when at least one method is available
    def prevent_stuttering(choices, assumes_or_asserts, ts, sink):
        no_choice = [Not(x) for x in choices.values()]
        conds = []
        for method in choices:
            if method in assumes_or_asserts:
                cond = assumes_or_asserts[method]
                if cond:
                    conds.append(And(*cond))
                else:
                    # Found a method that is always available
                    # Thus, stuttering is never allowed
                    conds = []
                    break
        condition = (
            _conjunct_smt((*no_choice, Or(*conds)))
            if conds else _conjunct_smt(no_choice))

        out = out_cl if sink == s_con_loses else out_cw
        ts.append(Transition(s0, condition, [], [out], sink))

    prevent_stuttering(symex_walker.env_choices, symex_walker.extern_assumes, env_ts, s_con_wins)  # noqa: E501
    prevent_stuttering(symex_walker.con_choices, symex_walker.intern_asserts, con_ts, s_con_loses)  # noqa: E501

    prg = Program(
        file_name, [s0, s_con_wins, s_con_loses], s0, init_values,
        env_ts, con_ts,
        env_events=events["extern"], con_events=events["intern"],
        out_events=out_actions)

    guarantees = [
        f"{mod.to_ltl()} (_METHOD_{method.name})"
        for method in tree.methods
        for mod in method.modalities
        if method.kind == "intern"]

    gf_methods_ext = [
        f"{mod.to_ltl()} (_METHOD_{method.name})"
        for method in tree.methods
        for mod in method.modalities
        if method.kind == "extern"]

    def add_method_prefixes(x):
        for method in tree.methods:
            x = x.replace(method.name, f"_METHOD_{method.name}")
        return x

    if tree.guarantees:
        guarantees.extend(add_method_prefixes(x) for x in tree.guarantees)

    return prg, guarantees, gf_methods_ext


def dsl_to_prog_and_tlsf(prg: Program, ltl: str = None, tlsf: str = None, dsl_guarantees=None, dsl_assumes=None):  # noqa: E501
    def state_to_str(x):
        if not isinstance(x, str) and hasattr(x, "__iter__"):
            return ", ".join(str[v] for v in list(x))
        return str(x)

    def tr_to_str(t, is_env):
        def remove_paren(s):
            s1 = str(s)
            return s1[1:-1] if s1.startswith('(') else s1

        result = f"{state_to_str(t.src)} -> {state_to_str(t.tgt)} [{remove_paren(t.condition)}"  # noqa: E501
        if t.action is not None and len(t.action) > 0:
            result += " $ " + ', '.join(map(remove_paren, t.action)).replace("=", ":=")  # noqa: E501
        if is_env and t.output is not None and len(t.output) > 0:
            result += " # " + ', '.join(map(remove_paren, t.output))
        return result + ']'

    other_states = ", ".join(
        state_to_str(s)
        for s in prg.states
        if s != prg.initial_state)

    def fmt_valuation(v: TypedValuation):
        typ = {
            "int": "integer", "nat": "integer", "natural": "integer",
            "bool": "boolean"}.get(str(v.type), str(v.type))
        return f"{v.name} : {typ} := {str(v.value).lower()}"

    valuations = [fmt_valuation(v) for v in prg.valuation]

    INDENT = " " * 16
    CN = ",\n" + INDENT
    SN = ";\n" + INDENT
    prog = f"""\
    program {prg.name.replace('.dsl', '')} {{
        STATES {{
            {state_to_str(prg.initial_state)}: init, {other_states}
        }}
        ENVIRONMENT EVENTS {{
            {', '.join(str(e) for e in prg.env_events)}
        }}
        CONTROLLER EVENTS {{
            {', '.join(str(e) for e in prg.con_events)}
        }}
        PROGRAM EVENTS {{
            {', '.join(str(e) for e in prg.out_events)}
        }}
        VALUATION {{
            {SN.join(valuations)}{';' if valuations else ''}

        }}
        ENVIRONMENT TRANSITIONS {{
            {CN.join(tr_to_str(t, True) for t in prg.env_transitions)}
        }}
        CONTROLLER TRANSITIONS {{
            {CN.join(tr_to_str(t, False) for t in prg.con_transitions)}
        }}
    }}
    """

    if tlsf is not None:
        return dedent(prog), tlsf

    assumes = (
        ["G (!_con_wins)"]
        if any(v.name == "_con_wins" for v in prg.out_events)
        else [])
    if dsl_assumes:
        assumes.extend(dsl_assumes)

    guarantees = (
        ["G (!_con_loses)"]
        if any(v.name == "_con_loses" for v in prg.out_events)
        else [])
    if ltl:
        guarantees.append(ltl)
    if dsl_guarantees:
        guarantees.extend(dsl_guarantees)

    tlsf = f"""
    INFO {{
        TITLE:       "{prg.name}"
        DESCRIPTION: "Generated from {prg.name} with syMTri"
        SEMANTICS:   Mealy
        TARGET:      Mealy
    }}

    MAIN {{

        INPUTS {{
            {SN.join(str(e) for e in prg.env_events)}{';' if prg.env_events else ''}
            {SN.join(str(e) for e in prg.out_events)}{';' if prg.out_events else ''}
        }}

        OUTPUTS {{
            {SN.join(str(e) for e in prg.con_events)}{';' if prg.con_events else ''}
        }}

        ASSUMPTIONS {{
            {SN.join(assumes)}{';' if assumes else ''}
        }}

        GUARANTEES {{
            {SN.join(guarantees)}{';' if (guarantees and guarantees[-1].strip()[-1]!=';') else ''}
        }}
    }}
    """

    return dedent(prog), dedent(tlsf)
