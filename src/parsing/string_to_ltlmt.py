import re

from tatsu.grammars import Grammar
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.math_op import MathOp
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
            return MathExpr(BiOp((node[0]), node[1], (node[2])))
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
