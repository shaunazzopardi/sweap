import re

from tatsu.grammars import Grammar
from tatsu.infos import ParserConfig
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.math_op import MathOp
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
        | number
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
        | number '.' number
        | '-' number '.' number
        | number
        | '-' number
        | atom
        ;

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
    number = /([0-9]+)/;
'''

parser: Grammar = compile(GRAMMAR)
math_config = ParserConfig(start='math_expression_eof')


def tuple_to_formula(node, hoa_flag, symbol_table) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)", node):
            return Value(node)
        elif not hoa_flag and re.match("[0-9]+(\.[0-9]+)?", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        if str(node[0]) == "-":
            return MathOp(UniOp(node[0], (node[1])))
        else:
            return UniOp(node[0], (node[1]))
    elif len(node) == 3:
        if node[0] == "(":
            return (node[1])
        else:
            if node[1] == "/":
                return Value(str(int(str(node[0].name).replace("f'", "")) / int(str(node[2]))))
            elif node[1] == ".":
                return (Value(str(node[0]) + str(node[1]) + str((node[2]))))

            if isinstance(node[0], Variable) and str(node[0]) in symbol_table.keys():
                if symbol_table[str(node[0])].type == "real":
                    if isinstance(node[2], Value) and "." not in str(node[2]):
                        node[2] = Value(str(node[2]) + ".0")
            elif isinstance(node[2], Variable) and str(node[2]) in symbol_table.keys():
                if symbol_table[str(node[2])].type == "real":
                    node[0].replace_math_exprs(symbol_table)
                    if isinstance(node[0], Value) and "." not in str(node[0]):
                        node[0] = Value(str(node[0]) + ".0")

            if re.match("(\+|\-|\*)", node[1]):
                return MathOp(BiOp((node[0]), node[1], (node[2])))
            elif re.match("(<|>|<=|>=|==)", node[1]):
                return MathExpr(BiOp(node[0], node[1], node[2]))
            else:
                return BiOp((node[0]), node[1], (node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


class Semantics:
    def __init__(self, hoa_flag=False, symbol_table={}):
        self.hoa_flag = hoa_flag
        self.symbol_table = symbol_table

    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast, self.hoa_flag, self.symbol_table)


def string_to_math_expression(text: str, symbol_table={}) -> MathExpr:
    formula = parser.parse(text, config=math_config, semantics=Semantics(False, symbol_table))
    return formula


def string_to_prop(text: str, hoa_flag=False) -> Formula:
    formula = parser.parse(text, semantics=Semantics(hoa_flag=hoa_flag))
    return formula
