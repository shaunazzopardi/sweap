import re
from enum import Enum

from dataclasses import dataclass
from typing import Optional

from pysmt.fnode import FNode
from pysmt.logics import BOOL
from pysmt.shortcuts import INT, BOOL, GE, LE, GT, LT, And, Int, TRUE, Symbol


@dataclass(frozen=True)
class Interval:
    lower: str = ""
    upper: str = ""
    lower_inclusive: bool = True
    upper_inclusive: bool = True

    def __init__(
        self,
        lower: str,
        upper: str,
        lower_inclusive: bool = True,
        upper_inclusive: bool = True,
    ):
        object.__setattr__(self, "lower", lower)
        object.__setattr__(self, "upper", upper)
        object.__setattr__(self, "lower_inclusive", lower_inclusive)
        object.__setattr__(self, "upper_inclusive", upper_inclusive)
        if lower == "" or upper == "":
            object.__setattr__(self, "inf", True)

    def __str__(self):
        l_bracket = "[" if self.lower_inclusive else "("
        r_bracket = "]" if self.upper_inclusive else ")"
        l = self.lower
        u = self.upper
        return f"{l_bracket}{l}, {u}{r_bracket}"

    def __eq__(self, other):
        if isinstance(other, Interval):
            return (
                self.lower == other.lower
                and self.upper == other.upper
                and self.lower_inclusive == other.lower_inclusive
                and self.upper_inclusive == other.upper_inclusive
            )
        return False

    def __hash__(self):
        return hash(
            (self.lower, self.upper, self.lower_inclusive, self.upper_inclusive)
        )


class Type:
    pass


SYMBOL_TABLE = dict[str, Type]


class BaseNumberTypes(Enum):
    integer = ("integer",)
    natural = ("natural",)


countable_number_types = [BaseNumberTypes.natural, BaseNumberTypes.integer]


class Boolean(Type):
    def __str__(self):
        return "boolean"

    def __eq__(self, other):
        if isinstance(other, Boolean):
            return True
        return False

    def __hash__(self):
        return hash("boolean")


class Number(Type):
    number_type: BaseNumberTypes
    interval: Optional[Interval]

    def __init__(self, number_type: BaseNumberTypes, interval: Optional[Interval]):
        self.number_type = number_type
        self.interval = interval

    def __str__(self):
        if self.interval:
            return str(self.number_type) + str(self.interval)
        else:
            return str(self.number_type)

    def __eq__(self, other):
        if isinstance(other, Number):
            return self.number_type == other.number_type and (
                self.interval == other.interval
                or (self.interval is None and other.interval is None)
            )
        return False

    def __hash__(self):
        return hash((self.number_type, self.interval))


def interval_range(num: Number) -> tuple[int, int]:
    if num.number_type not in countable_number_types:
        raise Exception(str(num.number_type) + " is not a countable number type.")
    elif num.interval.lower == "" or num.interval.upper == "":
        raise Exception("Cannot compute range for infinite interval.")
    else:
        lower = int(num.interval.lower)
        upper = int(num.interval.upper)
        if not num.interval.lower_inclusive:
            lower += 1
        if not num.interval.upper_inclusive:
            upper -= 1
        return lower, upper


def is_finite(type: Type) -> bool:
    if isinstance(type, Number):
        return (
            (
                type.number_type == BaseNumberTypes.integer
                or type.number_type == BaseNumberTypes.natural
            )
            and type.interval
            and not (type.interval.lower == "" or type.interval.upper == "")
        )
    elif isinstance(type, Boolean):
        return True
    else:
        return False


BOOLEAN: Boolean = Boolean()
NATURAL: Number = Number(BaseNumberTypes.natural, None)
INTEGER: Number = Number(BaseNumberTypes.integer, None)

natural_str = ["natural", "nat"]
natural_regex = "(" + "|".join(natural_str) + ")"

integer_str = ["integer", "int"]
integer_regex = "(" + "|".join(integer_str) + ")"

# interval_regex = r"((?P<lower_inc>[[\\(])(?P<lower>-?[0-9]*)\.\.(?P<upper>-?[0-9]*)(?P<upper_inc>[[\\(]))"
interval_regex = r"(?P<lower_inc>[\[\(])(?P<lower>-?[0-9]+)(?:\.\.)(?P<upper>-?[0-9]+)(?P<upper_inc>[\]\)])"
number_regex = f"({natural_regex}|{integer_regex})|({interval_regex})?"

bool_str = ["boolean", "bool"]
bool_regex = "(" + "|".join(bool_str) + ")"

type_regex = f"({number_regex}|{'|'.join(bool_str)})"


def typed_var_to_pysmt_type(var_name: str, type: Type) -> tuple[Symbol, FNode]:
    if type == INTEGER:
        return Symbol(var_name, INT), TRUE()
    elif type == BOOLEAN:
        return Symbol(var_name, BOOL), TRUE()
    elif type == NATURAL:
        return Symbol(var_name, INT), GE(Symbol(var_name, INT), Int(0))
    elif (
        isinstance(type, Number)
        and type.number_type in countable_number_types
        and type.interval
    ):
        return Symbol(var_name, INT), And(
            (
                GE(Symbol(var_name, INT), Int(int(type.interval.lower)))
                if type.interval.lower_inclusive
                else GT(Symbol(var_name, INT), Int(int(type.interval.lower)))
            ),
            (
                LE(Symbol(var_name, INT), Int(int(type.interval.upper)))
                if type.interval.upper_inclusive
                else LT(Symbol(var_name, INT), Int(int(type.interval.upper)))
            ),
        )
    else:
        raise NotImplementedError(f"Type {type} unsupported.")


def parse_type(type_str: str) -> Type:
    if type_str.lower() in natural_str:
        return NATURAL
    elif type_str.lower() in integer_str:
        return INTEGER
    elif type_str.lower() in bool_str:
        return BOOLEAN
    elif result := re.match(
        interval_regex,
        type_str,
        re.IGNORECASE,
    ):
        lower_inclusive = result.group("lower_inc") == "["
        lower_bound = result.group("lower")
        upper_bound = result.group("upper")
        upper_inclusive = result.group("upper_inc") == "]"
        if int(lower_bound) >= 0:
            basic_type = BaseNumberTypes.natural
        else:
            basic_type = BaseNumberTypes.integer

        return Number(
            basic_type,
            Interval(lower_bound, upper_bound, lower_inclusive, upper_inclusive),
        )
    else:
        raise Exception(
            type_str
            + " is not a valid type. Valid types are `bool'/`boolean', or numeric types `nat'/`natural' and `int'/`integer' possibly limited to an interval, e.g. `nat[-1, 10]', (capitilisation ignored)."
        )
