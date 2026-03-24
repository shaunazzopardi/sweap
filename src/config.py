import multiprocessing
import warnings

from prop_lang.uniop import UniOp
from prop_lang.variable import Variable

# Suppress pySMT/MathSAT noise for UF applications with boolean arguments.
# This warning is informational and can flood benchmark/test logs.
warnings.filterwarnings(
    "ignore",
    message=r"MathSAT convert\(\): UF with bool arguments have been translated",
    category=UserWarning,
    module=r"pysmt\.solvers\.msat",
)

env = Variable("env_turn")
con = UniOp("!", env)
init_state = Variable("init_state")

strix = "strix"
semml = "semml"
synthesis_backends = [semml, strix]
effects = "effects"
abstraction_backends = [effects]


class Config:
    _instance = None
    _backend = "semml"
    _finite_synthesis = False
    _prefer_ranking = False
    _only_structural = False
    _only_ranking = False
    _only_safety = False
    _eager_fairness = True
    _no_binary_enc = False
    _dual = False
    _dual2 = False
    _verify_controller = False
    _add_all_preds_in_prog = True
    _mc = False
    _debug = False
    _cnf_optimisations = False
    _parallelise_type = "processes"
    _name = None
    _log = None
    _cache_smt = False
    _opt_incremental_smt = True
    _opt_state_scopes = True
    _opt_chain_scopes = True
    _opt_location_constant_simplify = False
    _abstraction_backend = effects
    _synthesis_memory_limit_mb = None

    def _get_c_s(self):
        return self._cache_smt

    def _set_c_s(self, value):
        self._cache_smt = value

    def _get_opt_incremental_smt(self):
        return self._opt_incremental_smt

    def _set_opt_incremental_smt(self, value: bool):
        self._opt_incremental_smt = value

    def _get_opt_state_scopes(self):
        return self._opt_state_scopes

    def _set_opt_state_scopes(self, value: bool):
        self._opt_state_scopes = value

    def _get_opt_chain_scopes(self):
        return self._opt_chain_scopes

    def _set_opt_chain_scopes(self, value: bool):
        self._opt_chain_scopes = value

    def _get_opt_location_constant_simplify(self):
        return self._opt_location_constant_simplify

    def _set_opt_location_constant_simplify(self, value: bool):
        self._opt_location_constant_simplify = value

    def _get_b(self):
        return self._backend

    def _set_b(self, value):
        self._backend = value

    def _get_n(self):
        return self._name

    def _set_n(self, value: bool):
        self._name = value

    def _get_l(self):
        return self._log

    def _set_l(self, value: str):
        self._log = value

    def _get_f_s(self):
        return self._finite_synthesis

    def _set_f_s(self, value: bool):
        self._finite_synthesis = value

    def _get_d(self):
        return self._dual

    def _set_d(self, value: bool):
        self._dual = value

    def _get_d2(self):
        return self._dual2

    def _set_d2(self, value: bool):
        self._dual2 = value

    def _get_n_b_e(self):
        return self._no_binary_enc

    def _set_n_b_e(self, value: bool):
        self._no_binary_enc = value

    def _get_e_f(self):
        return self._eager_fairness

    def _set_e_f(self, value: bool):
        self._eager_fairness = value

    def _get_v_c(self):
        return self._verify_controller

    def _set_v_c(self, value: bool):
        self._verify_controller = value

    def _get_a_p_i_p(self):
        return self._add_all_preds_in_prog

    def _set_a_p_i_p(self, value: bool):
        self._add_all_preds_in_prog = value

    def _get_p_r(self):
        return self._prefer_ranking

    def _set_p_r(self, value: bool):
        self._prefer_ranking = value

    def _get_o_r(self):
        return self._only_ranking

    def _set_o_r(self, value: bool):
        self._only_ranking = value

    def _get_o_struct(self):
        return self._only_structural

    def _set_o_struct(self, value: bool):
        self._only_structural = value

    def _get_o_safety(self):
        return self._only_safety

    def _set_o_safety(self, value: bool):
        self._only_safety = value

    def _get_mc(self):
        return self._mc

    def _set_mc(self, value: bool):
        self._mc = value

    def _get_debug(self):
        return self._debug

    def _set_debug(self, value: bool):
        self._debug = value

    def _get_cnf_opt(self):
        return self._cnf_optimisations

    def _set_cnf_opt(self, value: bool):
        self._cnf_optimisations = value

    def _get_parallelise_type(self):
        return self._parallelise_type

    def _set_parallelise_type(self, value: str):
        self._parallelise_type = value

    def _get_abstraction_backend(self):
        return self._abstraction_backend

    def _set_abstraction_backend(self, value: str):
        self._abstraction_backend = value

    def _get_synthesis_memory_limit_mb(self):
        return self._synthesis_memory_limit_mb

    def _set_synthesis_memory_limit_mb(self, value):
        self._synthesis_memory_limit_mb = value

    def _do_nothing(self):
        pass

    name = property(_get_n, _set_n, _do_nothing, "")
    backend = property(_get_b, _set_b, _do_nothing, "")
    log = property(_get_l, _set_l, _do_nothing, "")
    finite_synthesis = property(_get_f_s, _set_f_s, _do_nothing, "")
    dual = property(_get_d, _set_d, _do_nothing, "")
    dual2 = property(_get_d2, _set_d2, _do_nothing, "")
    no_binary_enc = property(_get_n_b_e, _set_n_b_e, _do_nothing, "")
    prefer_ranking = property(_get_p_r, _set_p_r, _do_nothing, "")
    only_structural = property(_get_o_struct, _set_o_struct, _do_nothing, "")
    only_ranking = property(_get_o_r, _set_o_r, _do_nothing, "")
    only_safety = property(_get_o_safety, _set_o_safety, _do_nothing, "")
    eager_fairness = property(_get_e_f, _set_e_f, _do_nothing, "")
    verify_controller = property(_get_v_c, _set_v_c, _do_nothing, "")
    add_all_preds_in_prog = property(_get_a_p_i_p, _set_a_p_i_p, _do_nothing, "")
    mc = property(_get_mc, _set_mc, _do_nothing, "")
    debug = property(_get_debug, _set_debug, _do_nothing, "")
    cache_smt = property(_get_c_s, _set_c_s, _do_nothing, "")
    opt_incremental_smt = property(
        _get_opt_incremental_smt, _set_opt_incremental_smt, _do_nothing, ""
    )
    opt_state_scopes = property(
        _get_opt_state_scopes, _set_opt_state_scopes, _do_nothing, ""
    )
    opt_chain_scopes = property(
        _get_opt_chain_scopes, _set_opt_chain_scopes, _do_nothing, ""
    )
    opt_location_constant_simplify = property(
        _get_opt_location_constant_simplify,
        _set_opt_location_constant_simplify,
        _do_nothing,
        "",
    )
    cnf_optimisations = property(_get_cnf_opt, _set_cnf_opt, _do_nothing, "")
    parallelise_type = property(
        _get_parallelise_type, _set_parallelise_type, _do_nothing, ""
    )
    abstraction_backend = property(
        _get_abstraction_backend, _set_abstraction_backend, _do_nothing, ""
    )
    synthesis_memory_limit_mb = property(
        _get_synthesis_memory_limit_mb,
        _set_synthesis_memory_limit_mb,
        _do_nothing,
        "",
    )
    workers = 1  # multiprocessing.cpu_count()

    def __init__(self):
        raise RuntimeError("Use getConfig() instead")

    @classmethod
    def getConfig(cls):
        if cls._instance is None:
            cls._instance = cls.__new__(cls)
        return cls._instance
