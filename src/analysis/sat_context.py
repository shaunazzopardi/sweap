from analysis.smt_checker import check
from pysmt.shortcuts import And, Solver
from prop_lang.util import conjunct


class IncrementalSatContext:
    def __init__(self, symbol_table: dict, base_formula=None):
        self.symbol_table = symbol_table
        self.supports_scopes = True
        self._solver = Solver(name="msat")
        self._smt_cache = {}
        if base_formula is not None:
            self._solver.add_assertion(self._to_smt(base_formula))

    def _to_smt(self, formula):
        key = str(formula)
        cached = self._smt_cache.get(key)
        if cached is not None:
            return cached
        smt = And(*formula.to_smt(self.symbol_table))
        self._smt_cache[key] = smt
        return smt

    def is_sat(self, formula) -> bool:
        smt = self._to_smt(formula)
        self._solver.push()
        self._solver.add_assertion(smt)
        try:
            return self._solver.solve()
        finally:
            self._solver.pop()

    def close(self):
        self._solver.exit()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


class NonIncrementalSatContext:
    def __init__(self, symbol_table: dict, base_formula=None):
        self.symbol_table = symbol_table
        self.supports_scopes = False
        self._smt_cache = {}
        self._base_formula = base_formula

    def _to_smt(self, formula):
        key = str(formula)
        cached = self._smt_cache.get(key)
        if cached is not None:
            return cached
        smt = And(*formula.to_smt(self.symbol_table))
        self._smt_cache[key] = smt
        return smt

    def is_sat(self, formula) -> bool:
        if self._base_formula is None:
            return check(self._to_smt(formula))
        return check(self._to_smt(conjunct(self._base_formula, formula)))

    def close(self):
        return None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()
