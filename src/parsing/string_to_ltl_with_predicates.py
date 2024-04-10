import re

from tatsu.grammars import Grammar
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
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

    atom = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
    number = /(\d+|\d+\.\d+)/;
'''


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF)", node):
            return Value(node)
        elif re.match("[0-9]+(\.[0-9]+)?", node):
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        return UniOp(node[0], (node[1]))
    elif len(node) == 3:
        v0 = ((node[0]))
        v2 = ((node[2]))
        if v0 == None or v2 == None:
            print("None")
        if node[1] in ["+", "-", "*", "/", "<", ">", "<=", ">=", "==", "!="]:
            return MathExpr(BiOp((node[0]), node[1], (node[2])))
        elif node[0] == "(" and node[2] == ")":
            return node[1]
        else:
            return BiOp((node[0]), node[1], (node[2]))
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
