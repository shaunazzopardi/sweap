import re
import sys

from tatsu.grammars import Grammar
from tatsu.infos import ParserConfig
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.ops_and_rels import MathOps, BoolBiOps, BoolUniOps, MathRels
from prop_lang.types.values import BoolAtoms, natural_val_regex
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

sys.setrecursionlimit(20000)

GRAMMAR = r"""
    @@grammar::PROPLOGIC


    start = expression $ ;

    expression
        =
        | level_2 '->' expression
        | level_2 '<->' expression
        | level_2
        ;
    
    level_2
        =
        | level_1 '||' level_2
        | level_1 '|' level_2
        | level_1
        | atomic
        ;
    
    level_1 
        =
        | atomic '&&' level_1
        | atomic '&' level_1
        | atomic
        ;
    
    atomic
        =
        | '!' atomic
        | 'X' atomic
        | 'F' atomic
        | 'G' atomic
        | '(' @:expression ')'
        | math_expression '<' math_expression
        | math_expression '<=' math_expression
        | math_expression '>' math_expression
        | math_expression '>=' math_expression
        | math_expression '=' math_expression
        | math_expression '==' math_expression
        | math_expression '!=' math_expression
        | term
        ;


    term
        =
        | 'true'
        | 'false'
        | atom
        | number
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
        | '-' atom
        ;
        
    negated_atom 
        =
        | '!' atom $
        | atom $
        ;

    atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    number = /([0-9]+|[0-9]+\.[0-9]+)/;
"""

parser: Grammar = compile(GRAMMAR)
math_config = ParserConfig(start="math_expression_eof")
negated_atom_config = ParserConfig(start="negated_atom")

true_str = {"true", "tt", "TRUE", "True", "TT"}
false_str = {"false", "ff", "FALSE", "False", "FF"}
raw_bi_bool_ops_to_op = {
    "&": BoolBiOps.CONJ,
    "&&": BoolBiOps.CONJ,
    "|": BoolBiOps.DISJ,
    "||": BoolBiOps.DISJ,
    "->": BoolBiOps.IMPL,
    "<->": BoolBiOps.IFF,
    "iff": BoolBiOps.IFF,
}
raw_bi_math_ops_to_op = {
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
raw_bi_bool_math_ops_to_op = raw_bi_bool_ops_to_op | raw_bi_math_ops_to_op
raw_uni_bool_ops_to_op = {
    "!": BoolUniOps.NEG,
}
raw_uni_math_ops_to_op = {
    "-": MathOps.SUB,
}
raw_uni_bool_math_ops_to_op = raw_uni_bool_ops_to_op | raw_uni_math_ops_to_op


def tuple_to_formula(node, hoa_flag) -> Formula:
    if isinstance(node, str):
        if node in true_str:
            return Value(BoolAtoms.TRUE)
        elif node in false_str:
            return Value(BoolAtoms.FALSE)
        elif not hoa_flag and re.match(natural_val_regex, node):
            return Value(int(node))
        else:
            return Variable(node)
    elif len(node) == 2:
        if node[0] in raw_uni_bool_ops_to_op.keys():
            return UniOp(raw_uni_bool_ops_to_op[node[0]], (node[1]))
        elif node[0] in raw_uni_math_ops_to_op.keys():
            return MathExpr(UniOp(raw_uni_math_ops_to_op[node[0]], (node[1])))
        else:
            raise Exception("Invalid unary operator: " + str(node))
    elif len(node) == 3:
        if node[0] == "(":
            return node[1]
        else:
            if node[1] in raw_bi_math_ops_to_op.keys():
                return MathExpr(
                    BiOp((node[0]), raw_bi_math_ops_to_op[node[1]], (node[2]))
                )
            elif node[0] == "(" and node[2] == ")":
                return node[1]
            else:
                if node[1] in raw_bi_bool_ops_to_op.keys():
                    return BiOp((node[0]), raw_bi_bool_ops_to_op[node[1]], (node[2]))
                elif node[1] == "*":
                    if str(node[0]) == "-1":
                        return UniOp("-", (node[2]))
                    elif str(node[0]) == "1":
                        return node[2]
                elif node[1] == "/":
                    if str(node[2]) == "-1":
                        return UniOp("-", (node[1]))
                    elif str(node[2]) == "1":
                        return node[1]
                raise Exception("Cannot handled non LIA operators: " + str(node))
                # return BiOp((node[0]), node[1], (node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


class Semantics:
    def __init__(self, hoa_flag=False):
        self.hoa_flag = hoa_flag

    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast, self.hoa_flag)


def string_to_math_expression(text: str) -> MathExpr:
    formula = parser.parse(text, config=math_config, semantics=Semantics(False))
    return formula


def string_to_negated_atom(text: str) -> Formula:
    formula = parser.parse(text, config=negated_atom_config, semantics=Semantics(False))
    return formula


def string_to_prop(text: str, hoa_flag=False) -> Formula:
    formula = parser.parse(text, semantics=Semantics(hoa_flag=hoa_flag))
    return formula
