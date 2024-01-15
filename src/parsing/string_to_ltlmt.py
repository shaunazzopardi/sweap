import re
from collections import defaultdict
from itertools import combinations, product
from typing import Any

from pysmt.shortcuts import FALSE, TRUE, And, Iff, Not, Symbol
from tatsu.grammars import Grammar
from tatsu.objectmodel import Node
from tatsu.tool import compile
from tatsu.walkers import NodeWalker

from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.math_op import MathOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, normalize_ltl, stringify_pred
from prop_lang.value import Value
from prop_lang.variable import Variable

GRAMMAR = '''
    @@grammar::LTL


    start = expression $ ;


    expression
        =
        | level_2 '->' expression
        | level_2 '<->' expression
        | level_2
        ;

    level_2
        =
        | level_1 '|' level_2
        | level_1 '||' level_2
        | level_1
        ;

    level_1 
        =
        | level_0 '&&' level_1
        | level_0 '&' level_1
        | level_0
        ;

    level_0 
        =
        | atomic 'U' level_0
        | atomic 'W' level_0
        | atomic 'R' level_0
        | atomic 'M' level_0
        | atomic
        ;

    atomic
        =
        | '!' atomic
        | 'X' atomic
        | 'F' atomic
        | 'G' atomic
        | '(' @:expression ')'
        | boolean_term
        | action
        ;

    action
        = '[' atom ':=' math_expression ']';

    boolean_term
        =
        | 'true'
        | 'false'
        | math_predicate
        | atom
        ;
        
    math_predicate
        =
        math_expression '<' math_expression
        | math_expression '<=' math_expression
        | math_expression '>' math_expression
        | math_expression '>=' math_expression
        | math_expression '=' math_expression
        | math_expression '==' math_expression
        | math_expression '!=' math_expression
        ;

        
    math_expression
        = math_1 '+' math_expression
        | math_1 '-' math_expression
        | math_1
        ;
        
    math_expression_eof
        = math_expression $ ;
    
    math_1
        = math_0 '*' math_1
        | math_0 '/' math_1
        | math_0
        ;
    
    math_0
        = '(' math_expression ')'
        | number
        | '-' number
        | atom
        ;

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
    number = /(\d+|\d+\.\d+)/;
'''


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF|-?[0-9]+)", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        return UniOp(node[0], (node[1]))
    elif len(node) == 3:
        if re.match("^(<|>|<=|>=|==|=)$", node[1]):
            # Normalize == to =
            op = "=" if node[1] == "==" else node[1]
            return MathExpr(BiOp((node[0]), op, (node[2])))
        elif re.match("(!=)", node[1]):
                return UniOp("!", MathExpr(BiOp((node[0]), "=", (node[2]))))
        else:
            return BiOp((node[0]), node[1], (node[2]))
    elif len(node) == 5:
        return MathOp(BiOp((node[1]), node[2], node[3]))
    else:
        raise Exception("Invalid node: " + str(node))


parser: Grammar = compile(GRAMMAR)


class Semantics:
    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast)


def string_to_ltlmt(text: str) -> Formula:
    formula = parser.parse(text, semantics=Semantics())
    return formula


class ToProgram(NodeWalker):
    def __init__(self):
        super().__init__()
        self.env_events = set()
        self.updates = defaultdict(set)
        self.substitutions = {}
        self.checks = {}
        self.scan = True

    def walk_BiOp(self, node: BiOp):
        node.left = self.find_substitute(node.left)
        node.right = self.find_substitute(node.right)
        if node.op not in (">", ">=", "<", "<=", "==", "=", "!="):
            self.walk(node.left)
            self.walk(node.right)

    def find_substitute(self, n):
        if isinstance(n, MathOp) and n.formula in self.substitutions:
            return self.substitutions[n.formula]
        if isinstance(n, MathExpr) and n.formula in self.substitutions:
            return self.substitutions[n.formula]
        return self.substitutions.get(n, n)

    def walk_UniOp(self, node: UniOp):
        node.right = self.find_substitute(node.right)
        self.walk(node.right)

    def walk_Variable(self, node: Variable):
        if self.scan:
            self.env_events.add(Variable(node.name))

    def walk_MathExpr(self, node: MathExpr):
        if node.formula in self.substitutions:
            node.formula = self.substitutions[node.formula]
        self.walk(node.formula)

    def walk_MathOp(self, node: MathOp):
        if node.formula in self.substitutions:
            node.formula = self.substitutions[node.formula]
        elif (node.formula.op == ":="):
            # always add a chance to stutter
            stutter = BiOp(node.formula.left, ':=', node.formula.left)
            self.updates[node.formula.left.name].add(stutter)
            # add actual update
            self.updates[node.formula.left.name].add(node.formula)

    def ltlmt2prog(self, orig_formula: Formula, name="fromTSL"):
        # First pass to collect stuff
        self.walk(orig_formula)
        enum_updates = {
            var: set((stringify_pred(x).name.replace("pred__", "upd__"), x) for i, x in enumerate(ups))
            for var, ups in self.updates.items()}

        self.substitutions = self.checks | {
            u[1]: Variable(u[0])
            for var, ups in enum_updates.items()
            for u in ups}
        self.scan = False
        self.walk(orig_formula)

        con_events = [
            Variable(u[0])
            for ups in enum_updates.values() for u in ups]
        con_t = []

        # TODO how do we initialize?
        init_values = [TypedValuation(x, "integer", Value(0)) for x in self.updates]

        def mk_cond(names, determinize=True):
            if not determinize:
                return conjunct_formula_set(
                    x for x in con_events
                    if x.name in names)
            return conjunct_formula_set((
                x if x.name in names else UniOp("!", x)
                for x in con_events))

        for ups in product(*enum_updates.values()):
            con_t.append(Transition(
                'c0', mk_cond([u[0] for u in ups]),
                [u[1] for u in ups], [], 'e0'))

        env_t = [Transition(
            'e0', None,
            [BiOp(Variable(u), ":=", Variable(u)) for u in self.updates],
            [], 'c0'
        )]

        prog = Program(
            name, ['e0', 'c0'], 'e0', init_values, env_t, con_t,
            list(self.env_events), con_events, [], preprocess=True)

        formula = normalize_ltl(orig_formula)

        card_constraint = []
        for ups in enum_updates.values():
            up_vars = [Variable(x[0]) for x in ups]
            up_vars.sort(key=lambda x: x.name)
            at_least_one = disjunct_formula_set(up_vars)
            card_constraint.extend(
                BiOp(a, "->", UniOp("!", disjunct_formula_set([
                    b for b in up_vars if a != b])))
                for a in up_vars)
            card_constraint.append(at_least_one)

        card_constraint = conjunct_formula_set(
            UniOp("G", c) for c in card_constraint)

        if isinstance(formula, BiOp) and formula.op == "->":
            formula.right = BiOp(formula.right, "&&", card_constraint)
        else:
            formula = BiOp(formula, "&&", card_constraint)

        return prog, formula
