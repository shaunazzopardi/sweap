from pysmt.environment import Environment
from pysmt.shortcuts import Symbol
from pysmt.typing import INT

from prop_lang.types.types import INTEGER, typed_var_to_pysmt_type


def test_typed_symbols_belong_to_the_current_environment():
    with Environment():
        original, _ = typed_var_to_pysmt_type("shared", INTEGER)
        assert original is Symbol("shared", INT)
        with Environment():
            current, _ = typed_var_to_pysmt_type("shared", INTEGER)
            assert current is Symbol("shared", INT)
            assert current is not original
        restored, _ = typed_var_to_pysmt_type("shared", INTEGER)
        assert restored is original
