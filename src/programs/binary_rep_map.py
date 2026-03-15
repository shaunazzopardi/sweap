import math
import logging

from prop_lang.variable import Variable
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    dnf_safe,
    false,
    neg,
    propagate_negations,
    true,
)


class BinaryRepMap(dict):
    """Binary-encoding map with subset-disjunction simplification support."""
    _SUPPRESSED_TABLE_PREFIXES = (
        "formula_con_act_",
        "eq_con_",
        "sat_con_",
    )
    _TABLE_COMPLEMENT_PREVIEW_LIMIT = 6

    def __init__(self, *args, bin_vars=None, table_rhs_display=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.bin_vars = tuple(bin_vars) if bin_vars is not None else tuple()
        self._table_rhs_display = (
            dict(table_rhs_display) if table_rhs_display is not None else {}
        )

    def _normalise_boolean_formula(self, formula):
        if len(self.bin_vars) < 2:
            return formula
        return dnf_safe(
            propagate_negations(formula),
            {str(v): BOOLEAN for v in self.bin_vars},
        )

    def disjunct_for_keys(self, keys, *, use_complement: bool = True):
        selected = [k for k in keys if k in self]
        if len(selected) == 0:
            return false()
        selected_set = set(selected)
        if len(selected_set) == len(self):
            return true()

        if use_complement and len(selected_set) > len(self) / 2:
            complement = [self[k] for k in self.keys() if k not in selected_set]
            if len(complement) == 0:
                disj = true()
            else:
                disj = neg(disjunct_formula_set(complement))
        else:
            disj = disjunct_formula_set(self[k] for k in selected_set)

        return self._normalise_boolean_formula(disj)

    @staticmethod
    def should_emit_table(label: str) -> bool:
        label_s = str(label)
        return not any(
            label_s.startswith(prefix)
            for prefix in BinaryRepMap._SUPPRESSED_TABLE_PREFIXES
        )

    @staticmethod
    def _should_emit_for(label: str, force: bool) -> bool:
        return force or BinaryRepMap.should_emit_table(label)

    @staticmethod
    def _key_to_str(key):
        if isinstance(key, frozenset):
            return str(conjunct_formula_set(key))
        return str(key)

    @staticmethod
    def _is_contiguous(values: list[int]) -> bool:
        if len(values) == 0:
            return False
        return values == list(range(values[0], values[-1] + 1))

    @classmethod
    def _format_not_of_binary_codes(cls, codes: list[str]) -> str:
        if len(codes) == 0:
            return "TRUE"

        width = len(codes[0])
        if any(len(code) != width for code in codes):
            if len(codes) <= cls._TABLE_COMPLEMENT_PREVIEW_LIMIT:
                return "NOT(" + " OR ".join(codes) + ")"
            return (
                "NOT("
                + codes[0]
                + " OR ... OR "
                + codes[-1]
                + f") [{len(codes)} terms]"
            )

        if all(set(code).issubset({"0", "1"}) for code in codes):
            code_ints = sorted({int(code, 2) for code in codes})
            if len(code_ints) == len(codes) and cls._is_contiguous(code_ints):
                low = format(code_ints[0], f"0{width}b")
                high = format(code_ints[-1], f"0{width}b")
                if low == high:
                    return f"NOT({low})"
                return f"NOT([{low}..{high}])"

        if len(codes) <= cls._TABLE_COMPLEMENT_PREVIEW_LIMIT:
            return "NOT(" + " OR ".join(codes) + ")"
        return (
            "NOT("
            + codes[0]
            + " OR ... OR "
            + codes[-1]
            + f") [{len(codes)} terms]"
        )

    def _rhs_to_str(self, key, value):
        return self._table_rhs_display.get(key, str(value))

    def format_table(self, label: str) -> str:
        title = f"Binary representation map [{label}]"
        if len(self.bin_vars) > 0:
            bit_positions = ", ".join(
                f"{idx}:{var}" for idx, var in enumerate(self.bin_vars)
            )
            title += f" [bits L->R: {bit_positions}]"
        col1_header = "Predicate"
        col2_header = "Binary representation"
        rows = [(self._key_to_str(k), self._rhs_to_str(k, v)) for k, v in self.items()]

        col1_width = max([len(col1_header)] + [len(r[0]) for r in rows])
        col2_width = max([len(col2_header)] + [len(r[1]) for r in rows])

        top = "+" + "-" * (col1_width + 2) + "+" + "-" * (col2_width + 2) + "+"
        hdr = (
            "| "
            + col1_header.ljust(col1_width)
            + " | "
            + col2_header.ljust(col2_width)
            + " |"
        )
        sep = "+" + "=" * (col1_width + 2) + "+" + "=" * (col2_width + 2) + "+"
        body = [
            "| " + left.ljust(col1_width) + " | " + right.ljust(col2_width) + " |"
            for left, right in rows
        ]
        return "\n".join([title, top, hdr, sep] + body + [top])

    def log_table(self, label: str, *, force: bool = False):
        if not self._should_emit_for(label, force):
            return
        logging.info(self.format_table(label))

    def print_table(self, label: str, *, force: bool = False):
        if not self._should_emit_for(label, force):
            return
        print(self.format_table(label))

    @classmethod
    def build_binary_rep(cls, vars_to_encode, label: str):
        vars_sorted = sorted(vars_to_encode, key=lambda x: str(x))
        if len(vars_sorted) == 0:
            raise Exception("Cannot create binary representation of empty set")

        width = max(1, math.ceil(math.log(len(vars_sorted), 2)))
        bin_vars = [Variable(label + str(i)) for i in range(0, width)]
        rep = cls(bin_vars=bin_vars)
        base = "{0:0" + str(width) + "b}"
        binary_codes = {}

        for i, v in enumerate(vars_sorted):
            binary_code = base.format(i)
            binary_codes[v] = binary_code
            bit_formula = None
            for j, bit in enumerate(binary_code):
                lit = neg(bin_vars[j]) if bit == "0" else bin_vars[j]
                bit_formula = lit if bit_formula is None else conjunct(bit_formula, lit)
            rep[v] = bit_formula
            rep._table_rhs_display[v] = binary_code

        # For non-power-of-two domains, replace the last encoding by the
        # complement of all previous encodings to keep it exact and compact.
        if len(vars_sorted) > 2 and len(vars_sorted) < 2**width:
            last = vars_sorted[-1]
            others = [k for k in rep.keys() if k != last]
            rep[last] = rep._normalise_boolean_formula(
                neg(rep.disjunct_for_keys(others, use_complement=False))
            )
            rep._table_rhs_display[last] = cls._format_not_of_binary_codes(
                [binary_codes[k] for k in others]
            )

        return bin_vars, rep
