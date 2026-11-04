"""Keep independent test cases from sharing configuration and solver state."""

import pytest
from pysmt.shortcuts import reset_env

from config import Config
from programs.util import reset_caches as reset_program_caches
from prop_lang.util import reset_caches as reset_formula_caches
from prop_lang.types.types import _typed_var_to_pysmt_type_cached


@pytest.fixture(autouse=True)
def isolated_configuration():
    conf = Config.getConfig()
    original = vars(conf).copy()
    yield
    # Config properties use backing attributes and no-op deleters, so
    # patch.object on a property can leave its backing value changed.
    vars(conf).clear()
    vars(conf).update(original)


@pytest.fixture(autouse=True)
def isolated_smt_environment():
    reset_env()
    reset_formula_caches()
    reset_program_caches()
    _typed_var_to_pysmt_type_cached.cache_clear()
    yield
    reset_formula_caches()
    reset_program_caches()
    _typed_var_to_pysmt_type_cached.cache_clear()
    reset_env()
