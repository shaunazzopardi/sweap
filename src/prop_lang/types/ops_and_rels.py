from enum import Enum
from typing import Union


class StringableEnum(Enum):
    def __str__(self):
        return self.value[0]

    def __add__(self, other):
        return self.value[0] + str(other)

    def __repr__(self):
        return self.value[0]

    def __radd__(self, other):
        return str(other) + self.value[0]

    def __eq__(self, other):
        if isinstance(other, StringableEnum):
            return self.value[0] == other.value[0]
        elif isinstance(other, str):
            return self.value[0] == other
        return False

    def __hash__(self):
        return hash(self.value[0])


class MathOps(StringableEnum):
    ADD = ("+",)
    SUB = ("-",)

    def to_nuxmv(self):
        return self.value[0]


def parse_math_op(math_op_str: str) -> MathOps:
    if math_op_str.lower() == "+":
        return MathOps.ADD
    elif math_op_str.lower() == "-":
        return MathOps.SUB
    else:
        raise Exception(
            math_op_str
            + " is not a valid mathematical operation. Valid operations are `+' or `-'."
        )


class BoolBiOps(StringableEnum):
    CONJ = ("&",)
    DISJ = ("|",)
    IMPL = ("->",)
    IFF = ("<->",)

    def to_nuxmv(self):
        match self:
            case BoolBiOps.CONJ:
                return "&"
            case BoolBiOps.DISJ:
                return "|"
            case BoolBiOps.IMPL:
                return "->"
            case BoolBiOps.IFF:
                return "<->"


class BoolUniOps(StringableEnum):
    NEG = ("!",)

    def to_nuxmv(self):
        return self.value[0]


def parse_bool_bi_op(bool_op_str: str) -> BoolBiOps:
    if bool_op_str.lower() in ["&", "&&"]:
        return BoolBiOps.CONJ
    elif bool_op_str.lower() in ["|", "||"]:
        return BoolBiOps.DISJ
    elif bool_op_str.lower() in ["->", "=>"]:
        return BoolBiOps.IMPL
    elif bool_op_str.lower() in ["<->", "<=>"]:
        return BoolBiOps.IFF
    else:
        raise Exception(
            bool_op_str
            + " is not a valid boolean operation. Valid operations are `&`/`&&`, `|`/`||`, `->`/`=>`, `<->`/`<=>`/`iff`/`==`."
        )


def parse_bool_uni_op(bool_op_str: str) -> BoolUniOps:
    if bool_op_str.lower() == "!":
        return BoolUniOps.NEG
    else:
        raise Exception(
            bool_op_str
            + " is not a valid boolean unary operation. Valid operation is `!`."
        )


class MathRels(StringableEnum):
    LT = ("<",)
    LE = ("<=",)
    GT = (">",)
    GE = (">=",)
    EQ = ("=",)
    NEQ = ("!=",)

    def to_nuxmv(self):
        return self.value[0]


def parse_math_rels(math_rels_str: str) -> MathRels:
    if math_rels_str.lower() == "<":
        return MathRels.LT
    elif math_rels_str.lower() == "<=":
        return MathRels.LE
    elif math_rels_str.lower() == ">":
        return MathRels.GT
    elif math_rels_str.lower() == ">=":
        return MathRels.GE
    elif math_rels_str.lower() in ["=", "=="]:
        return MathRels.EQ
    elif math_rels_str.lower() == "!=":
        return MathRels.NEQ
    else:
        raise Exception(
            math_rels_str
            + " is not a valid mathematical relation. Valid mathematical relation are `<', `<=', `>', `>=', or `='/`=='."
        )


class LTLBiOps(StringableEnum):
    U = ("U",)
    W = ("W",)
    R = ("R",)
    M = ("M",)

    def to_nuxmv(self):
        return self.value[0]


def parse_ltl_bi_op(ltl_bi_op_str: str) -> LTLBiOps:
    if ltl_bi_op_str == "U":
        return LTLBiOps.U
    elif ltl_bi_op_str == "W":
        return LTLBiOps.W
    elif ltl_bi_op_str == "R":
        return LTLBiOps.R
    elif ltl_bi_op_str == "M":
        return LTLBiOps.M
    else:
        raise Exception(
            ltl_bi_op_str
            + " is not a valid LTL binary operation. Valid operations are `U' (Until), `W' (Weak Until), `R' (Release), or `M' (Mighty release)."
        )


class LTLUniOps(StringableEnum):
    X = ("X",)
    F = ("F",)
    G = ("G",)

    def to_nuxmv(self):
        return self.value[0]


def parse_ltl_uni_op(ltl_uni_op_str: str) -> LTLUniOps:
    if ltl_uni_op_str == "X":
        return LTLUniOps.X
    elif ltl_uni_op_str == "F":
        return LTLUniOps.F
    elif ltl_uni_op_str == "G":
        return LTLUniOps.G
    else:
        raise Exception(
            ltl_uni_op_str
            + " is not a valid LTL unary operation. Valid operations are `X' (Next), `F' (Eventually), or `G' (Globally)."
        )


Bi_ops_rels = Union[BoolBiOps, MathOps, MathRels, LTLBiOps]


def bi_ops_rels_parser(op_str: str):
    try:
        return parse_bool_bi_op(op_str)
    except Exception:
        pass
    try:
        return parse_math_op(op_str)
    except Exception:
        pass
    try:
        return parse_math_rels(op_str)
    except Exception:
        pass
    try:
        return parse_ltl_bi_op(op_str)
    except Exception:
        pass
    raise Exception(
        op_str
        + " is not a valid binary operation or relation. Valid operations are `&' (and), `|' (or), `->' (implies), `<->' (iff), `U' (Until), `W' (Weak Until), `R' (Release), or `M' (Mighty release). Valid mathematical operations are `+' or `-'. Valid mathematical relations are `<', `<=', `>', `>=', `=' or `!='."
    )


Uni_ops_rels = Union[BoolUniOps, MathOps, LTLUniOps]


def uni_ops_rels_parser(op_str: str):
    try:
        return parse_bool_uni_op(op_str)
    except Exception:
        pass
    try:
        return parse_math_op(op_str)
    except Exception:
        pass
    try:
        return parse_ltl_uni_op(op_str)
    except Exception:
        pass
    raise Exception(
        op_str
        + " is not a valid unary operation. Valid operations are `!' (not), `X' (Next), `F' (Eventually), or `G' (Globally). Valid mathematical operations are `-'"
    )
