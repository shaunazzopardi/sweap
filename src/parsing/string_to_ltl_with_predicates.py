import re

from tatsu.grammars import Grammar
from tatsu.tool import compile

from parsing.string_to_ltl import (
    true_str,
    false_str,
    raw_uni_ops_to_op,
    raw_bi_ops_to_op,
)
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.ops_and_rels import MathOps, MathRels
from prop_lang.types.values import BoolAtoms, natural_val_regex
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

GRAMMAR = r"""
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
        | math_expression '<' math_expression
        | math_expression '<=' math_expression
        | math_expression '>' math_expression
        | math_expression '>=' math_expression
        | math_expression '=' math_expression
        | math_expression '==' math_expression
        | math_expression '!=' math_expression
        | '(' @:expression ')'
        | term
        ;


    term
        =
        | 'true'
        | 'false'
        | atom
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

    atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    number = /([0-9]+|[0-9]+\.[0-9]+)/;
"""

raw_math_uni_ops_to_op = {"-": MathOps.SUB}
raw_math_bi_ops_to_op = {
    "+": MathOps.ADD,
    "-": MathOps.SUB,
    "<": MathRels.LT,
    "<=": MathRels.LE,
    ">": MathRels.GT,
    ">=": MathRels.GE,
    "=": MathRels.EQ,
    "==": MathRels.EQ,
    "!=": MathRels.NEQ,
}


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if node in true_str:
            return Value(BoolAtoms.TRUE)
        elif node in false_str:
            return Value(BoolAtoms.FALSE)
        elif re.match(natural_val_regex, node):
            return Value(int(node))
        else:
            return Variable(node)
    elif len(node) == 2:
        if node[0] in raw_math_uni_ops_to_op.keys():
            return MathExpr(UniOp(raw_math_uni_ops_to_op[node[0]], (node[1])))
        elif node[0] in raw_uni_ops_to_op.keys():
            return UniOp(raw_uni_ops_to_op[node[0]], (node[1]))
        else:
            raise Exception("Invalid node: " + str(node))
    elif len(node) == 3:
        if node[0] == "(" and node[2] == ")":
            return node[1]
        elif node[1] in raw_math_bi_ops_to_op.keys():
            return MathExpr(BiOp((node[0]), raw_math_bi_ops_to_op[node[1]], (node[2])))
        elif node[1] in raw_bi_ops_to_op.keys():
            return BiOp((node[0]), raw_bi_ops_to_op[node[1]], (node[2]))
        else:
            raise Exception("Invalid node: " + str(node))
            # return BiOp((node[0]), node[1], (node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


parser: Grammar = compile(GRAMMAR)


class Semantics:
    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast)


def string_to_ltl_with_predicates(text: str) -> Formula:
    formula = parser.parse(text, semantics=Semantics())
    return formula
