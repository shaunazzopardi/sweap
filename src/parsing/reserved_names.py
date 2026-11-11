"""Keep user identifiers out of namespaces used by generated program symbols."""

from collections.abc import Collection, Iterable

from parsing.keywords import regex_keywords
from prop_lang.formula import Formula
from prop_lang.variable import Variable


GENERATED_PREFIXES = (
    "curr_", "int_", "game_", "eval_minigame_", "minigame_", "con_", "c_",
    "controller_guard_", "controller_act_", "program_q_",
    "comp_", "inp_comp_",
)

FRAMEWORK_NAMES = frozenset({
    "eval", "init_state", "second_state", "compatible", "program_state",
    "strategy_state", "prog_m", "strat_m", "init_choice_logic",
    "__init", "__trans", "__invar",
})

BOOLEAN_LITERAL_NAMES = frozenset({"true", "false", "TRUE", "FALSE", "True", "False"})

# nuXmv 2.2 user manual, chapter 2 (identifier and keyword spelling is case-sensitive):
# https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf
# Include inherited NuSMV temporal keywords and underscore spellings used by
# timed expressions in the grammar appendix as well.
NUXMV_RESERVED_WORDS = frozenset("""
    @F~ @O~ A ABF ABG abs acos AF AG array asin atan ASSIGN AX bool boolean
    B BU case Clock clock COMPASSION COMPID COMPUTE COMPWFF CONSTANTS CONSTARRAY
    CONSTRAINT cos count CTLSPEC CTLWFF DEFINE E EBF EBG EF EG esac EX exp
    extend F FAIRNESS FALSE floor FROZENVAR FUN G H IN in INIT init Integer
    integer INVAR INVARSPEC ISA ITYPE IVAR JUSTICE ln LTLSPEC LTLWFF MAX max
    MDEFINE MIN min MIRROR mod MODULE NAME next NEXTWFF noncontinuous O of
    PRED PREDICATES pi pow PSLSPEC PARSYNTH READ Real real resize S SAT self
    signed SIMPWFF sin sizeof SPEC sqrt swconst T tan time toint TRANS TRUE
    typeof U union unsigned URGENT uwconst V VALID VAR W Word word word1 WRITE
    X xnor xor X~ Y Y~ Z at_next at_last time_since time_until process
""".split()) | frozenset({"at next", "at last", "time since", "time until"})


def validate_declared_names(names: Iterable[str]) -> None:
    for name in names:
        if name in BOOLEAN_LITERAL_NAMES:
            raise ValueError(f"Boolean literal {name!r} cannot be used as an identifier.")


def is_reserved_name(name: str) -> bool:
    return (
        name in BOOLEAN_LITERAL_NAMES
        or name in NUXMV_RESERVED_WORDS
        or name in FRAMEWORK_NAMES
        or name.startswith("q_")
        or any(pattern.match(name) for pattern in regex_keywords)
        or name.startswith(GENERATED_PREFIXES)
        or name.endswith("_prev")
    )


def fresh_name(name: str, occupied: Collection[str]) -> str:
    while name in occupied:
        name = "res_" + name
    return name


def reserved_name_mapping(names: Iterable[str]) -> dict[str, str]:
    """Allocate against all original names so renaming never merges declarations."""
    occupied = set(names)
    validate_declared_names(occupied)
    result = {}
    for name in sorted(occupied):
        if is_reserved_name(name):
            if name.endswith("_prev"):
                # Prefixing alone leaves the name in the lookback namespace.
                suffix = "_res"
                target = name + suffix
                if is_reserved_name(target):
                    target = "res_" + target
                while target in occupied:
                    target += suffix
            else:
                target = fresh_name("res_" + name, occupied)
            occupied.add(target)
            result[name] = target
    return result


def rename_formula(formula: Formula, names: dict[str, str]) -> Formula:
    def replace(node):
        if isinstance(node, Variable):
            base = node.name.rstrip("'")
            # Exact declarations take precedence over implicit history aliases.
            while base not in names and base.endswith("_prev"):
                base = base.removesuffix("_prev")
            if base in names:
                return Variable(names[base] + node.name[len(base):])
        return None

    return formula.replace_formulas(replace)


def rename_tree(value, names):
    """Rename formulas and identifier strings in parsed expression trees."""
    if isinstance(value, Formula):
        return rename_formula(value, names)
    if isinstance(value, str):
        return names.get(value, value)
    if isinstance(value, (list, tuple, set, frozenset)):
        return type(value)(rename_tree(v, names) for v in value)
    if isinstance(value, dict):
        return {rename_tree(k, names): rename_tree(v, names) for k, v in value.items()}
    return value
