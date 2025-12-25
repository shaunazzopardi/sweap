import re
from enum import Enum

from tatsu.grammars import Grammar
from tatsu.tool import compile

from parsing.keywords import regex_keywords, is_keyword
from prop_lang.biop import BiOp
from prop_lang.factory import create_mathrel
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.uniop import UniOp
from prop_lang.update_formula import UpdateFormula

from prop_lang.value import Value
from prop_lang.variable import Variable

GRAMMAR = """
    @@grammar::LTL
    
    start_placeholder

    macros
        = f_macro
        | 'assume' '{' { expression [';'] }* '}'
        | 'always assume' '{' { expression [';'] }* '}'
        | 'guarantee' '{' { expression [';'] }* '}'
        | 'always guarantee' '{' { expression [';'] }* '}'
        ;

    f_macro
        = atom '=' (math_predicate | math_expression | expression | math_0) ';';

    expression
        = biop_expression
        | level_0
        ;
    
    biop_expression
        = level_0 ('->' | '<->' | '||' | '|' | '&&' | '&') expression;

    level_0 
        = ltl_biop
        | atomic
        ;
        
    ltl_biop
        = atomic ('U' | 'W' | 'R' | 'M') level_0 ;

    atomic
        = '(' @:expression ')'
        | ltl_uniop
        | boolean_term
        | action
        ;

    ltl_uniop
        = ('!' | 'X' | 'F' | 'G') atomic
        ;

    action_ltlmt
        = '[' atom '<-' expression ']'
        | '[' atom '<-' math_expression ']';
    
    action_issy
        = '[' math_update_expression_issy ']';

    boolean_term
        = 'true'
        | 'false'
        | math_predicate
        | atom
        | '!' boolean_term
        ;

    math_predicate_ltl
        = math_expression_ltl ('>=' | '<=' | '>' | '<' | '==' | '=' | '!=') math_expression_ltl;

    math_predicate_ltlmt
        = ('lt' | 'le' | 'gt' | 'ge' | 'eq' | 'neq') math_expression_ltlmt math_expression_ltlmt;

    math_expression_ltl
        = math_0 ('+' | '-' | '*') math_expression_ltl
        | math_0
        ;

    math_expression_ltlmt
        = ('add' | 'sub' | 'mul') math_0 math_expression_ltlmt
        | math_0
        ;

    math_0
        = number
        | atom
        | '(' math_expression ')'
        ;
    
    math_update_expression_issy
        = math_0_issy_update ('+' | '-' | '*') math_update_expression_issy
        | math_0_issy_update
        ;

    math_0_issy_update
        = number
        | atom
        | next_atom
        | '(' math_update_expression_issy ')'
        ;
    
    math_expression_eof
        = math_expression $ ;

    atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    next_atom = /_?[a-zA-Z][a-zA-Z0-9_-]*'/;
    number_ltl = /-?([0-9]+|[0-9]+\\.[0-9]+)/;
    number_ltlmt = /(i|c)m?([0-9]+|[0-9]+\\.[0-9]+)\\(\\)/;
"""

translate_ops = {
    "eq": "=",
    "neq": "!=",
    "lt": "<",
    "le": "<=",
    "gt": ">",
    "ge": ">=",
    "add": "+",
    "sub": "-",
    "mul": "-",
}

unary_operators = {"!", "-"}
unary_LTL_operators = {"G", "F", "X"}
binary_operators = {"&&", "||", "&", "|", "->", "<->"}
binary_LTL_operators = {"U", "W", "R", "M"}


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF|m?[0-9]+)", node):
            if node[0] == "m":
                return UniOp("-", Value(node[1:]))
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        if isinstance(node[0], str) and (
            node[0] in unary_operators or node[0] in unary_LTL_operators
        ):
            return UniOp(node[0], (node[1]))
        else:
            return node
    elif len(node) == 3:
        if isinstance(node[0], str) and node[0] in translate_ops.keys():
            return create_mathrel(node[1], translate_ops[node[0]], node[2])
        elif isinstance(node[1], str) and (
            node[1] in binary_operators or node[1] in binary_LTL_operators
        ):
            return BiOp((node[0]), node[1], (node[2]))
        elif node[0] == "(" and node[2] == ")":
            return node[1]
        else:
            return node
    elif len(node) == 5 and node[2] == "<-":
        if not isinstance(node[1], Variable):
            raise Exception(
                "The left hand side of an update must be a variable: "
                + " ".join(map(str, node))
            )
        return Update((node[1]), node[3])
    else:
        return node


parser_ltl: Grammar = compile(
    GRAMMAR.replace("| action", "").replace(
        "start_placeholder", "start = expression $ ;"
    )
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
)
parser_ltlmt: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = { macros }* $ ;")
    + "\n math_expression = math_expression_ltlmt ; "
    + "\n number = number_ltlmt ; "
    + "\n math_predicate = math_predicate_ltlmt ;"
    + "\n action = action_ltlmt;"
)
parser_issy_ltl: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = expression $ ;")
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
    + "\n action = action_issy;"
)


class Semantics:
    def number_ltl(self, ast):
        if ast[0] == "-":
            return UniOp("-", Value(int(ast[1:])))
        return Value(int(ast))

    def number_ltlmt(self, ast):
        if ast[0] == "m":
            return UniOp("-", Value(int(ast[1:])))

        return Value(int(ast[1]))

    def next_atom(self, ast):
        return Variable(ast)

    def atom(self, ast):
        if ast == "":
            raise Exception("Unhandled empty AST node")
        if not is_keyword(ast):
            return Variable(ast)
        else:
            raise Exception("Keyword used as atom: " + ast)

    def math_expression_ltlmt(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif len(ast) == 3:
            if ast[0] in translate_ops.keys():
                return MathExpr(BiOp(ast[1], translate_ops[ast[0]], ast[2]))
        raise Exception("Unhandled AST node: " + str(ast))

    def math_predicate_ltlmt(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif len(ast) == 3:
            if ast[0] in translate_ops.keys():
                return create_mathrel(ast[1], translate_ops[ast[0]], ast[2])
        raise Exception("Unhandled AST node: " + str(ast))

    def math_predicate_ltl(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif len(ast) == 3:
            return create_mathrel(ast[0], ast[1], ast[2])
        raise Exception("Unhandled AST node: " + str(ast))

    def math_expression_ltl(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif len(ast) == 3:
            return MathExpr(BiOp(ast[0], ast[1], ast[2]))
        raise Exception("Unhandled AST node: " + str(ast))

    def boolean_term(self, ast):
        if ast == "true":
            return Value(BoolAtoms.TRUE)
        elif ast == "false":
            return Value(BoolAtoms.FALSE)
        elif isinstance(ast, Formula):
            return ast
        elif ast[0] == "!":
            return UniOp("!", ast[1])
        else:
            return ast

    def action_issy(self, ast):
        return UpdateFormula(ast[1])

    def action_ltlmt(self, ast):
        if any(
            o
            for o in ast[3].ops_used()
            if o in binary_LTL_operators or o in unary_LTL_operators
        ):
            raise Exception("AST node: " + str(ast) + " contains LTL operators")
        else:
            return Update(ast[1], ast[3])

    def ltl_uniop(self, ast):
        return UniOp(ast[0], ast[1])

    def ltl_biop(self, ast):
        return BiOp(ast[0], ast[1], ast[2])

    def biop_expression(self, ast):
        return BiOp(ast[0], ast[1], ast[2])

    def f_macro(self, ast):
        return ast

    def macros(self, ast):
        return ast

    def start(self, ast):
        return ast

    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "(" and ast[2] == ")":
            return ast[1]
        else:
            raise Exception("Unhandled AST node: " + str(ast))


class lang(Enum):
    LTL_with_preds = 1
    LTLMT = 2
    ISSY_LTL = 3


def string_to_ltl_with_predicates(text: str) -> Formula:
    return parser_ltl.parse(
        text,
        semantics=Semantics(),
        comments="(\\/\\*.*?\\*\\/)",
        eol_comments="\\/\\/.*?(\n|$)",
    )


def string_to_ltlmt(text: str) -> Formula:
    text = re.sub("//.*$", "", text)
    regex_keywords.extend(
        list(
            map(
                re.compile,
                [r"eval$", r"q_.+"],
            )
        )
    )
    return parser_ltlmt.parse(
        text,
        semantics=Semantics(),
        comments="(\\/\\*.*?\\*\\/)",
        eol_comments="\\/\\/.*?(\n|$)",
    )


def string_to_issy_ltl(text: str) -> Formula:
    return parser_issy_ltl.parse(
        text,
        semantics=Semantics(),
        comments="(\\/\\*.*?\\*\\/)",
        eol_comments="\\/\\/.*?(\n|$)",
    )
