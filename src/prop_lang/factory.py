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
    if isinstance(lhs, Value):
        if isinstance(rhs, Value):
            return Value(int(lhs.val) * int(rhs.val))

        val = int(lhs.val)
        var = rhs
    elif isinstance(rhs, Value):
        if isinstance(lhs, Value):
            return Value(int(lhs.val) * int(rhs.val))
        val = int(rhs.val)
        var = lhs
    else:
        raise Exception(
            "We cannot handle multiplication between variables: "
            + str(lhs)
            + " * "
            + str(rhs)
        )
    if val == -1:
        return UniOp("-", var)
    elif val == 1:
        return var
    elif val == 0:
        return Value(0)
    # handle positive multiplication by unrolling
    elif val > 0:
        c = val
        result = rhs
        for _ in range(c - 1):
            result = BiOp(result, "+", var)
        return result
    # hangle negative multiplication by unrolling
    elif val < 0:
        c = abs(val)
        result = rhs
        for _ in range(c - 1):
            result = BiOp(result, "+", var)
        return UniOp("-", result)
    else:
        raise Exception(
            "I cannot resolve this multiplication: " + str(lhs) + ", " + str(rhs)
        )
