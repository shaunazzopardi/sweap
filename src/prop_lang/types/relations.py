from enum import Enum


class MathRels(Enum):
    LT = ("<",)
    LE = ("<=",)
    GT = (">",)
    GE = (">=",)
    EQ = ("=",)


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
    else:
        raise Exception(
            math_rels_str
            + " is not a valid mathematical relation. Valid mathematical relation are `<', `<=', `>', `>=', or `='/`=='."
        )
