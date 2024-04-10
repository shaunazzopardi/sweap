import re

from tatsu.grammars import Grammar
from tatsu.infos import ParserConfig
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable
import sys
sys.setrecursionlimit(20000)

GRAMMAR = '''
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
        ;
        
    negated_atom 
        =
        | '!' atom $
        | atom $
        ;

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
    number = /(\d+|\d+\.\d+)/;
'''

parser: Grammar = compile(GRAMMAR)
math_config = ParserConfig(start='math_expression_eof')
negated_atom_config = ParserConfig(start='negated_atom')


def tuple_to_formula(node, hoa_flag) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)", node):
            return Value(node)
        elif not hoa_flag and re.match("[0-9]+(\.[0-9]+)?", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        return UniOp(node[0], (node[1]))
    elif len(node) == 3:
        if node[0] == "(":
            return (node[1])
        else:
            v0 = ((node[0]))
            v2 = ((node[2]))
            if v0 == None or v2 == None:
                print("None")
            if node[1] in ["+", "-", "*", "/", "<", ">", "<=", ">=", "==", "=", "!="]:
                return MathExpr(BiOp((node[0]), node[1].replace("==", "="), (node[2])))
            elif node[0] == "(" and node[2] == ")":
                return node[1]
            else:
                return BiOp((node[0]), node[1], (node[2]))
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


def string_to_negated_atom(text: str) -> MathExpr:
    formula = parser.parse(text, config=negated_atom_config, semantics=Semantics(False))
    return formula


def string_to_prop(text: str, hoa_flag=False) -> Formula:
    formula = parser.parse(text, semantics=Semantics(hoa_flag=hoa_flag))
    return formula
