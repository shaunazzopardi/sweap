import re

from tatsu.grammars import Grammar
from tatsu.tool import compile

from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import LTLBiOps, LTLUniOps, BoolBiOps, BoolUniOps
from prop_lang.types.values import BoolAtoms, natural_val_regex
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

GRAMMAR = """
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
        | term
        ;


    term
        =
        | 'true'
        | 'false'
        | atom
        ;

    atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
"""

true_str = {"true", "tt", "TRUE", "True", "TT"}
false_str = {"false", "ff", "FALSE", "False", "FF"}
raw_bi_ops_to_op = {
    "U": LTLBiOps.U,
    "W": LTLBiOps.W,
    "R": LTLBiOps.R,
    "M": LTLBiOps.M,
    "X": LTLUniOps.X,
    "F": LTLUniOps.F,
    "G": LTLUniOps.G,
    "&": BoolBiOps.CONJ,
    "&&": BoolBiOps.CONJ,
    "|": BoolBiOps.DISJ,
    "||": BoolBiOps.DISJ,
    "->": BoolBiOps.IMPL,
    "<->": BoolBiOps.IFF,
    "iff": BoolBiOps.IFF,
}
raw_uni_ops_to_op = {
    "!": BoolUniOps.NEG,
    "X": LTLUniOps.X,
    "F": LTLUniOps.F,
    "G": LTLUniOps.G,
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
        return UniOp(raw_uni_ops_to_op[node[0]], (node[1]))
    elif len(node) == 3:
        return BiOp((node[0]), raw_bi_ops_to_op[node[1]], (node[2]))
    else:
        raise Exception("Invalid node: " + str(node))


parser: Grammar = compile(GRAMMAR)


class Semantics:
    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast)


def string_to_ltl(text: str) -> Formula:
    formula = parser.parse(text, semantics=Semantics())
    return formula
