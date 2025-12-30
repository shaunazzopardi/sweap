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

from prop_lang.util import conjunct_formula_set
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

    boolean_term_not_issy
        = 'true'
        | 'false'
        | math_predicate
        | atom
        | '!' boolean_term
        ;
    
    
    boolean_term_issy
        = 'true'
        | 'false'
        | math_predicate
        | next_atom
        | atom
        | '!' boolean_term_issy
        ;

    math_predicate_issy = '[' math_predicate_ltl ']' | '[' boolean_term ']' | issy_keep;
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

    math_0_ltl_mt
        = number
        | atom
        | '(' math_expression ')'
        ;

    math_0_issy
        = number
        | issy_keep
        | next_atom
        | boolean_term
        | atom
        | '(' math_expression_ltl ')'
        ;
    
    issy_keep
        = 'keep' '(' { atom } ')' ;
    
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


parser_ltl: Grammar = compile(
    GRAMMAR.replace("| action", "").replace(
        "start_placeholder", "start = expression $ ;"
    )
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_not_issy ;"
)
parser_ltlmt: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = { macros }* $ ;")
    + "\n math_expression = math_expression_ltlmt ; "
    + "\n number = number_ltlmt ; "
    + "\n math_predicate = math_predicate_ltlmt ;"
    + "\n action = action_ltlmt;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_not_issy ;"
)
parser_issy_ltl: Grammar = compile(
    GRAMMAR.replace("| action", "| next_atom").replace(
        "start_placeholder", "start = expression $ ;"
    )
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_issy ;"
    + "\n math_0 = math_0_issy ;"
    + "\n boolean_term = boolean_term_issy ;"
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

    def boolean_term_not_issy(self, ast):
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

    def boolean_term_issy(self, ast):
        return self.boolean_term_not_issy(ast)

    def math_predicate_issy(self, ast):
        if isinstance(ast, Formula):
            return ast
        if any(v for v in ast[1].variablesin() if v.is_next()):
            # return UpdateFormula(ast[1])
            return ast[1]
        else:
            return ast[1]

    def issy_keep(self, ast):
        stutters = []
        for at in ast[2]:
            stutters.append(BiOp(Variable(at.name + "'"), "=", at))
        return conjunct_formula_set(stutters)

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
