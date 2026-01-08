from typing import Union
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.value import Value
from prop_lang.variable import Variable
from prop_lang.formula import Formula


def create_update(left: Formula, right: Formula) -> Update:
    return Update(left, right)


def create_var(v: str) -> Variable:
    return Variable(v)


def create_value(c: Union[int, float, str]) -> Value:
    return Value(c)


def create_biop(left: Formula, op: str, right: Formula) -> BiOp:
    return BiOp(left, op, right)


def create_mathrel(left: Formula, op: str, right: Formula) -> MathExpr:
    if op == "*":
        if isinstance(left, Value):
            c = int(left.val)
            if c == 0:
                return MathExpr(Value("0"))
            f = right
        elif isinstance(right, Value):
            c = int(right.val)
            if c == 0:
                return MathExpr(Value("0"))
            f = left
        else:
            raise ValueError(
                "Multiplication operator '*' can only be used with a Value and a Variable."
            )

        # Handle edge cases
        if c == 0:
            return MathExpr(Value("0"))
        if c == 1:
            return MathExpr(f)
        if c == -1:
            return MathExpr(UniOp("-", f))

        # Handle negative multipliers
        if c < 0:
            abs_c = abs(c)
            result = f
            for _ in range(abs_c - 1):
                result = BiOp(result, "+", f)
            return MathExpr(UniOp("-", result))

        # Handle positive multipliers > 1
        result = f
        for _ in range(c - 1):
            result = BiOp(result, "+", f)
        return MathExpr(result)
    else:
        return MathExpr(BiOp(left, op, right))


def create_uniop(op: str, v: Formula) -> UniOp:
    return UniOp(op, v)


def create_neg_no(v: Formula) -> UniOp:
    return create_uniop("-", v)


def _mult(lhs, rhs):
    lhs_str = str(lhs)
    rhs_str = str(rhs)
    if lhs_str == "-1":
        return UniOp("-", rhs)
    elif rhs_str == "-1":
        return UniOp("-", lhs)
    elif lhs_str == "1":
        return rhs
    elif rhs_str == "1":
        return lhs
    elif lhs_str == "0" or rhs_str == "0":
        return Value(0)
    elif lhs_str.isdigit() and rhs_str.isdigit():
        return Value(int(lhs_str) * int(rhs_str))
    # handle positive multiplication by unrolling
    elif lhs_str.isdigit() and int(lhs_str) > 1:
        c = int(lhs_str)
        result = rhs
        for _ in range(c - 1):
            result = BiOp(result, "+", rhs)
        return result
    elif rhs_str.isdigit() and int(rhs_str) > 1:
        c = int(rhs_str)
        result = lhs
        for _ in range(c - 1):
            result = BiOp(result, "+", lhs)
        return result
    # hangle negative multiplication by unrolling
    elif lhs_str.isdigit() and int(lhs_str) < 0:
        c = abs(int(lhs_str))
        result = rhs
        for _ in range(c - 1):
            result = BiOp(result, "+", rhs)
        return UniOp("-", result)
    elif rhs_str.isdigit() and int(rhs_str) < 0:
        c = abs(int(rhs_str))
        result = lhs
        for _ in range(c - 1):
            result = BiOp(result, "+", lhs)
        return UniOp("-", result)
    else:
        raise Exception("Multiplication by non negative value: " + str((lhs, rhs)))
