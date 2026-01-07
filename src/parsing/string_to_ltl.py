import logging
import re
import sys
from enum import Enum

from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.shortcuts import serialize, And
from tatsu.grammars import Grammar
from tatsu.infos import ParserConfig
from tatsu.tool import compile

from parsing.keywords import regex_keywords, is_keyword
from prop_lang.biop import BiOp
from prop_lang.factory import create_mathrel
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

# TODO: this is needed for parsing HOA transitions
#       look into optimising the parser to not need this
sys.setrecursionlimit(20000)

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
        = impl_expression
        ;

    impl_expression
        = or_expression {('->' | '<->') or_expression}*
        ;

    or_expression
        = and_expression {('||' | '|') and_expression}*
        ;

    and_expression
        = ltl_expression {('&&' | '&') ltl_expression}*
        ;

    ltl_expression
        = ltl_biop
        | ltl_uniop
        | basic_expression
        ;

    ltl_biop
        = ltl_uniop {('U' | 'W' | 'R' | 'M') (ltl_uniop)}+
        ;

    ltl_uniop
        = {('!' | 'X' | 'F' | 'G')}* basic_expression
        ;

    basic_expression
        = bool_vals
        | '(' expression ')'
        | math_predicate
        | boolean_term
        ;
        
    atomic
        = '(' @:expression ')'
        | boolean_term
        | math_predicate
        ;

    action_ltlmt
        = '[' atom '<-' expression ']'
        | '[' atom '<-' math_expression ']';

    boolean_term_ltl
        = bool_vals
        | atom
        | '!' boolean_term
        | expression ('=' | '!=') expression
        | math_predicate
        ;
    
    boolean_term_ltlmt
        = action_ltlmt
        | bool_vals
        | math_predicate
        | atom
        | '!' boolean_term
        ;
    
    boolean_term_issy
        = bool_vals
        | math_predicate_ltl
        | next_atom
        | atom
        | '!' boolean_term_issy
        ;
        
    bool_vals = 'true' | 'false' | 'TRUE' | 'FALSE' | 'True' | 'False' ;

    math_predicate_issy = '[' bool_vals ']'
                        | '[' (next_atom | atom) ('=' | '!=') ('true' | 'false') ']'
                        | '!' '[' (next_atom | atom) ('=' | '!=') ('true' | 'false') ']'
                        | '[' boolean_term ']'
                        | '!' '[' boolean_term ']'
                        | issy_keep;
                        
    math_predicate_ltl
        = math_expression_ltl ('>=' | '<=' | '>' | '<' | '==' | '=' | '!=') math_expression_ltl;

    math_predicate_ltlmt
        = ('lt' | 'le' | 'gt' | 'ge' | 'eq' | 'neq') math_expression_ltlmt math_expression_ltlmt;

    math_expression_ltl
        = math_0 {('+' | '-' | '*') math_0}*
        ;

    math_expression_ltlmt
        = ('add' | 'sub' | 'mul') math_0 math_expression_ltlmt
        | math_0
        ;

    math_0_ltl_mt
        = math_expression
        | number
        | atom
        | '(' math_0_ltl_mt ')'
        ;

    math_0_issy
        = number
        | next_atom
        | atom
        | '(' math_expression_ltl ')'
        ;
    
    issy_keep
        = 'keep' '(' { atom } ')' ;
            
    negated_atom 
        =
        | '!' atom $
        | atom $
        ;
        
    math_expression_eof
        = math_expression $ ;
    
    atom = normal_atom ;
    
    normal_atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    hoa_atom = /[0-9]+/;
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

parser_hoa: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = expression $ ;").replace(
        "atom = normal_atom", "atom = hoa_atom"
    )
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_ltl ;"
)
parser_ltl: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = expression $ ;")
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_ltl ;"
)
parser_ltlmt: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = { macros }* $ ;")
    + "\n math_expression = math_expression_ltlmt ; "
    + "\n number = number_ltlmt ; "
    + "\n math_predicate = math_predicate_ltlmt ;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_ltlmt ;"
)
parser_issy_ltl: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = expression $ ;")
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_issy ;"
    + "\n math_0 = math_0_issy ;"
    + "\n boolean_term = boolean_term_issy ;"
)
math_config = ParserConfig(start="math_expression_eof")
negated_atom_config = ParserConfig(start="negated_atom")


class Semantics:
    def __init__(self, prop=False, keyword_checking=True):
        self.prop = prop
        self.keyword_checking = keyword_checking

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

    def normal_atom(self, ast):
        if ast == "":
            raise Exception("Unhandled empty AST node")
        if not self.keyword_checking or not is_keyword(ast):
            return Variable(ast)
        else:
            raise Exception("Keyword used as atom: " + ast)

    def hoa_atom(self, ast):
        return self.normal_atom(ast)

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
        if len(ast[1]) == 0:
            return ast[0]
        if ast[1][0][0] == "*":
            return self.mult(ast)
        ret = ast[0]
        for op, f in ast[1]:
            ret = BiOp(ret, op, f)
        return ret

    def mult(self, ast):
        ret = ast[0]
        ret_str = str(ret)
        for _, f in ast[1]:
            f_str = str(f)
            if ret_str == "-1":
                ret = UniOp("-", f)
            elif f_str == "-1":
                ret = UniOp("-", ret)
            elif ret_str == "1":
                ret = f
            elif f_str == "1":
                ret = ret
            elif ret_str == "0" or f_str == "0":
                ret = Value(0)
            elif ret_str.isdigit() and f_str.isdigit():
                ret = Value(int(ret_str) * int(f_str))
            else:
                raise Exception("Multiplication by non-stant value: " + str(ast))
        return ret

    def boolean_term_ltl(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "!":
            return UniOp("!", ast[1])
        elif len(ast) == 3:
            return BiOp(ast[0], ast[1], ast[2])
        else:
            return ast

    def boolean_term_ltlmt(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "!":
            return UniOp("!", ast[1])
        else:
            return ast

    def boolean_term_issy(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "!":
            return UniOp("!", ast[1])
        else:
            return ast

    def bool_vals(self, ast: str):
        if ast.lower() == "true":
            return Value(BoolAtoms.TRUE)
        else:
            return Value(BoolAtoms.FALSE)

    def math_predicate_issy(self, ast):
        if isinstance(ast, Formula):
            return ast
        if len(ast) == 5:
            val = Value(BoolAtoms.TRUE) if ast[3] == "true" else Value(BoolAtoms.FALSE)
            return BiOp(ast[1], ast[2], val)
        elif len(ast) == 6:
            val = Value(BoolAtoms.TRUE) if ast[4] == "true" else Value(BoolAtoms.FALSE)
            return UniOp("!", (BiOp(ast[2], ast[3], val)))
        elif ast[0] == "!":
            return UniOp("!", ast[1])
        elif isinstance(ast[1], str):
            return self.bool_vals(ast[1])
        if any(v for v in ast[1].variablesin() if v.is_next()):
            return ast[1]
        else:
            return ast[1]

    def issy_keep(self, ast):
        stutters = None
        for at in ast[2]:
            if not stutters:
                stutters = BiOp(Variable(at.name + "'"), "=", at)
            else:
                stutters = BiOp(stutters, "&", BiOp(Variable(at.name + "'"), "=", at))
        return stutters

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
        if len(ast[0]) == 0:
            return ast[1]
        if self.prop and any(i for i in ast[0] if i != "!"):
            raise Exception("LTL unary operator in propositional formula: " + str(ast))
        res = UniOp(ast[0][-1], ast[1])
        for op in reversed(ast[0][:-1]):
            res = UniOp(op, res)
        return res

    def ltl_biop(self, ast):
        if isinstance(ast, Formula):
            return ast
        if self.prop:
            raise Exception("LTL binary operator in propositional formula: " + str(ast))
        ret = ast[0]
        for op, f in ast[1]:
            ret = BiOp(ret, op, f)
        return ret

    def or_expression(self, ast):
        if len(ast[1]) == 0:
            return ast[0]
        else:
            f = ast[0]
            for op, g in ast[1]:
                f = BiOp(f, op, g)
            return f

    def and_expression(self, ast):
        if len(ast[1]) == 0:
            return ast[0]
        else:
            f = ast[0]
            for op, g in ast[1]:
                f = BiOp(f, op, g)
            return f

    def impl_expression(self, ast):
        if len(ast[1]) == 0:
            return ast[0]
        else:
            f = ast[0]
            for op, g in ast[1]:
                f = BiOp(f, op, g)
            return f
        # return implies_formula_set([ast[0]] + list(map(lambda x: x[1], ast[1])))

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


def string_to_prop(text: str, hoa_flag=False) -> Formula:
    parser = parser_ltl if not hoa_flag else parser_hoa
    return parser.parse(
        text,
        semantics=Semantics(True, False),
        comments="(\\/\\*.*?\\*\\/)",
        eol_comments="\\/\\/.*?(\n|$)",
    )


def string_to_math_expression(text: str) -> MathExpr:
    formula = parser_ltl.parse(
        text, config=math_config, semantics=Semantics(False, False)
    )
    return formula


def string_to_negated_atom(text: str) -> Formula:
    formula = parser_ltl.parse(
        text, config=negated_atom_config, semantics=Semantics(False, False)
    )
    return formula


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


def fnode_to_issy_formula(fnode: FNode) -> Formula:
    fnode_str = serialize(fnode).replace("True", "true").replace("False", "false")
    fnode_str = re.sub(r"\\?'(?![ |)])", "", fnode_str)
    to_ret = string_to_issy_ltl(fnode_str)

    return to_ret


def simplify_issy_formula_with_math(formula, symbol_table):
    with Environment() as environ:
        simplified = environ.simplifier.simplify(And(*formula.to_smt(symbol_table)))
        try:
            to_formula = fnode_to_issy_formula(simplified)
        except Exception as e:
            to_formula = fnode_to_issy_formula(simplified)
            logging.info(str(e))
        return to_formula
