from prop_lang.util import neg
from prop_lang.variable import Variable


env = Variable("env_turn")
con = neg(env)
init_state = Variable("init_state")


class Config:
    _instance = None
    _prefer_ranking = True
    _only_structural = False
    _only_ranking = False
    _only_safety = False
    _eager_fairness = True
    _mc = False
    _debug = False
    _cnf_optimisations = False
    _parallelise_type = "processes"

    def _get_e_f(self):
        return self._eager_fairness

    def _set_e_f(self, value: bool):
        self._eager_fairness = value

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

    def _do_nothing(self):
        pass

    prefer_ranking = property(_get_p_r, _set_p_r, _do_nothing, "")
    only_structural = property(_get_o_struct, _set_o_struct, _do_nothing, "")
    only_ranking = property(_get_o_r, _set_o_r, _do_nothing, "")
    only_safety = property(_get_o_safety, _set_o_safety, _do_nothing, "")
    eager_fairness = property(_get_e_f, _set_e_f, _do_nothing, "")
    mc = property(_get_mc, _set_mc, _do_nothing, "")
    debug = property(_get_debug, _set_debug, _do_nothing, "")
    cnf_optimisations = property(_get_cnf_opt, _set_cnf_opt, _do_nothing, "")
    parallelise_type = property(_get_parallelise_type, _set_parallelise_type, _do_nothing, "")

    def __init__(self):
        raise RuntimeError("Use getConfig() instead")

    @classmethod
    def getConfig(cls):
        if cls._instance is None:
            cls._instance = cls.__new__(cls)
        return cls._instance
