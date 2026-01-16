from ast import For
import re
from enum import Enum
import sys

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

from prop_lang.util import fnode_to_formula
from prop_lang.value import Value
from prop_lang.variable import Variable

sys.setrecursionlimit(20000)
GRAMMAR = r"""
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
        = iff_expression
        ;
    
    iff_expression
        = ('<->' | '<=>')%{ impl_expression }+
        ;
    
    impl_expression
        = ('->' | '=>')%{ or_expression }+
        ;

    or_expression
        = ('||' | '|')%{ and_expression }+
        ;

    and_expression
        = ('&&' | '&')%{ ltl_biop }+
        ;
        
    ltl_biop
        = ('U' | 'W' | 'R' | 'M')%{ ltl_uniop }+
        ;

    ltl_uniop
        = &('!' | 'X' | 'F' | 'G') {ltl_uniop_op}+ atomic
        | atomic
        ;

    ltl_uniop_op
        = '!' | 'X' | 'F' | 'G'
        ;

    atomic
        = '(' @:expression ')'
        | boolean_term
        ;

    action_ltlmt
        = '[' atom '<-' (math_expression | expression) ']';

    boolean_term_ltl
        = '!' boolean_term
        | math_predicate
        | bool_vals
        | atom !('>=' | '<=' | '>' | '<' !'->' | '==' | '=' | '!=')
        ;
    
    boolean_term_ltlmt
        = action_ltlmt
        | bool_vals
        | math_predicate
        | atom
        | '!' boolean_term
        ;
    
    boolean_term_issy
        = math_predicate
        | bool_vals
        | atom
        | '!' boolean_term_issy
        ;

    bool_vals = 'true' | 'false' | 'TRUE' | 'FALSE' | 'True' | 'False' ;

    math_predicate_issy = '[' (math_predicate_ltl | boolean_term) ']'
                        | issy_keep
                        | math_predicate_ltl;

    math_predicate_ltl
        = math_expression_ltl ('>=' | '<=' | '>' | '<' | '==' | '=' | '!=') math_expression_ltl;

    math_predicate_ltlmt
        = ('lt' | 'le' | 'gt' | 'ge' | 'eq' | 'neq') math_expression_ltlmt math_expression_ltlmt;

    math_expression_ltl
        = ('+' | '-' !'>')%{ math_term_ltl }+
        | math_term_ltl
        ;

    math_term_ltl
        = '*'%{ math_factor_ltl }+
        | math_factor_ltl
        ;

    math_factor_ltl
        = '-' math_factor_ltl
        | math_0
        ;

    math_expression_ltlmt
        = ('add' | 'sub' | 'mul') math_0 math_0 
        | math_0;

    math_0_ltl_mt
        = '(' @:math_expression ')'
        | number
        | atom 
        ;

    math_0_issy
        = issy_keep
        | atom
        | number
        | '(' @:math_expression_ltl ')'
        ;
    
    issy_keep
        = 'keep' '(' { atom } ')' ;
    
    negated_atom 
        = '!' atom $
        | atom $
        ;
    
    math_expression_eof
        = math_expression $ ;

    atom = normal_atom ;
    
    normal_atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    hoa_atom = /[0-9]+/;
    next_atom = /_?[a-zA-Z][a-zA-Z0-9_-]*'/;
    next_or_now_atom = /_?[a-zA-Z][a-zA-Z0-9_-]*'?/;
    number_ltl = /-?([0-9]+|[0-9]+\.[0-9]+)/;
    number_ltlmt = /(i|c)m?([0-9]+|[0-9]+\.[0-9]+)\(\)/;
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
    "mul": "*",
}

unary_operators = {"!", "-"}
unary_LTL_operators = {"G", "F", "X"}
binary_operators = {"&&", "||", "&", "|", "->", "<->"}
binary_LTL_operators = {"U", "W", "R", "M"}


parser_hoa: Grammar = compile(
    GRAMMAR.replace("start_placeholder", "start = expression $ ;")
    .replace("atom = normal_atom", "atom = hoa_atom")
    .replace("| action", "")
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_ltl ;"
    + "\n math_0 = math_0_ltl_mt ;"
    + "\n boolean_term = boolean_term_ltl ;"
)
parser_ltl: Grammar = compile(
    GRAMMAR.replace("| action", "").replace(
        "start_placeholder", "start = expression $ ;"
    )
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
    GRAMMAR.replace("atom = normal_atom", "atom = next_or_now_atom").replace(
        "start_placeholder", "start = expression $ ;"
    )
    + "\n number = number_ltl ; "
    + "\n math_expression = math_expression_ltl ; "
    + "\n math_predicate = math_predicate_issy ;"
    + "\n math_0 = math_0_issy ;"
    + "\n boolean_term = boolean_term_issy ;"
)
math_config = ParserConfig(start="math_expression_eof")
negated_atom_config = ParserConfig(start="negated_atom")


class Semantics:
    def __init__(self, prop: bool = False, keyword_checking: bool = True):
        self.prop = prop
        self.keyword_checking = keyword_checking

    def _fold_join(self, ast, right_assoc=False):
        if isinstance(ast, Formula):
            return ast
        if not isinstance(ast, list):
            return ast
        if len(ast) == 1:
            return ast[0]
        if len(ast) % 2 == 0:
            raise Exception("Unexpected join AST shape: " + str(ast))
        if right_assoc:
            rhs = ast[-1]
            for i in range(len(ast) - 2, 0, -2):
                op = ast[i]
                lhs = ast[i - 1]
                rhs = BiOp(lhs, op, rhs)
            return rhs
        lhs = ast[0]
        for i in range(1, len(ast), 2):
            op = ast[i]
            rhs = ast[i + 1]
            if op == "*":
                lhs = self._mult(lhs, rhs)
                continue
            try:
                lhs = BiOp(lhs, op, rhs)
            except Exception as e:
                print(str(lhs) + " " + str(op) + " " + str(rhs))
                raise e
        return lhs

    def number_ltl(self, ast):
        if ast[0] == "-":
            return UniOp("-", Value(int(ast[1:])))
        return Value(int(ast))

    def number_ltlmt(self, ast):
        if ast[0] == "m":
            return UniOp("-", Value(int(ast[1:])))

        return Value(int(ast[1]))

    def _maybe_bool_literal(self, ast):
        if ast in ["true", "TRUE", "True"]:
            return Value(BoolAtoms.TRUE)
        if ast in ["false", "FALSE", "False"]:
            return Value(BoolAtoms.FALSE)
        return None

    def next_atom(self, ast):
        literal = self._maybe_bool_literal(ast)
        if literal is not None:
            return literal
        if not self.keyword_checking or not is_keyword(ast):
            return Variable(ast)

    def next_or_now_atom(self, ast):
        literal = self._maybe_bool_literal(ast)
        if literal is not None:
            return literal
        if not self.keyword_checking or not is_keyword(ast):
            return Variable(ast)

    def normal_atom(self, ast):
        literal = self._maybe_bool_literal(ast)
        if literal is not None:
            return literal
        if not self.keyword_checking or not is_keyword(ast):
            return Variable(ast)

    def hoa_atom(self, ast):
        return self.normal_atom(ast)

    def math_expression_ltlmt(self, ast):
        if isinstance(ast, Formula):
            return ast

        return create_mathrel(ast[1], translate_ops[ast[0]], ast[2])

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
        return self._fold_join(ast)

    def math_term_ltl(self, ast):
        return self._fold_join(ast)

    def math_factor_ltl(self, ast):
        if isinstance(ast, Formula):
            return ast
        return UniOp("-", ast[1])

    def math_factor_ltlmt(self, ast):
        return ast

    def boolean_term_ltl(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "!":
            return UniOp("!", ast[1])
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

    def bool_vals(self, ast):
        if ast.lower() == "true":
            return Value(BoolAtoms.TRUE)
        else:
            return Value(BoolAtoms.FALSE)

    def math_predicate_issy(self, ast):
        if isinstance(ast, Formula):
            return ast
        if len(ast) >= 2 and ast[0] == "[" and isinstance(ast[1], Formula):
            return ast[1]
        if (
            len(ast) >= 3
            and ast[0] == "!"
            and ast[1] == "["
            and isinstance(ast[2], Formula)
        ):
            return UniOp("!", ast[2])
        if len(ast) == 5:
            val = Value(BoolAtoms.TRUE) if ast[3] == "true" else Value(BoolAtoms.FALSE)
            return BiOp(ast[1], ast[2], val)
        elif len(ast) == 6:
            val = Value(BoolAtoms.TRUE) if ast[4] == "true" else Value(BoolAtoms.FALSE)
            return UniOp("!", BiOp(ast[2], ast[3], val))
        elif ast[0] == "!":
            return UniOp("!", ast[1])
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

    def ltl_uniop_op(self, ast):
        return ast

    def ltl_uniop(self, ast):
        if isinstance(ast, Formula):
            return ast

        ops = ast[0]
        right = ast[1]
        if len(ops) == 0:
            return right
        if self.prop and any(i for i in ops if i != "!"):
            raise Exception("LTL unary operator in propositional formula: " + str(ast))
        res = UniOp(ops[-1], right)
        for op in reversed(ops[:-1]):
            res = UniOp(op, res)
        return res

    def ltl_biop(self, ast):
        if not (isinstance(ast, list) and len(ast) == 1):
            if self.prop:
                raise Exception(
                    "LTL binary operator in propositional formula: " + str(ast)
                )
        return self._fold_join(ast)

    def or_expression(self, ast):
        return self._fold_join(ast)

    def and_expression(self, ast):
        return self._fold_join(ast)

    def impl_expression(self, ast):
        return self._fold_join(ast)

    def iff_expression(self, ast):
        return self._fold_join(ast)

    def f_macro(self, ast):
        return ast

    def macros(self, ast):
        return ast

    def start(self, ast):
        return ast

    def negated_atom(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return UniOp("!", ast[1])

    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        elif ast[0] == "(" and ast[2] == ")":
            return ast[1]
        elif ast[0] == "!" and isinstance(ast[1], Formula):
            return UniOp("!", ast[1])
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


def string_to_prop(text: str, hoa_flag: bool = False) -> Formula:
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
    def strip_outer_parens(s: str) -> str:
        s = s.strip()
        if not (s.startswith("(") and s.endswith(")")):
            return s
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return s
        if depth == 0:
            return s[1:-1].strip()
        return s

    def normalize_ltlmt_text(s: str) -> str:
        prev = None
        s = s.strip()
        while s != prev:
            prev = s
            s = strip_outer_parens(s)
            s = re.sub(r"!\s*!", "", s)
            s = re.sub(r"\(\s*\(([^()]+)\)\s*\)", r"(\1)", s)
        return s

    text = re.sub("//.*$", "", text)
    text = normalize_ltlmt_text(text)
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
    # fnode_str = serialize(fnode).replace("True", "true").replace("False", "false")
    # fnode_str = re.sub(r"\\?'(?![ |)])", "", fnode_str)
    to_ret = fnode_to_formula(fnode)

    return to_ret


def simplify_issy_formula_with_math(formula, symbol_table):
    with Environment() as environ:
        simplified = environ.simplifier.simplify(And(*formula.to_smt(symbol_table)))
        try:
            to_formula = fnode_to_issy_formula(simplified)
        except Exception as e:
            to_formula = fnode_to_issy_formula(simplified)
        return to_formula
