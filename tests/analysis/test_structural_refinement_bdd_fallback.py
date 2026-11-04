from unittest.mock import patch

from analysis.refinement.fairness_refinement.structural_refinement import (
    structural_refinement,
)
from parsing.string_to_ltl import string_to_ltl_with_predicates as parse
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import normalise_formula, true
from prop_lang.value import Value
from prop_lang.variable import Variable


def test_structural_refinement_without_bdd_preserves_constraints():
    """Missing BDD support must preserve the original loop exit condition."""
    exit_condition = parse('!(!(cl <= 0) & (cl <= 49) & !(cl <= 0))')
    def refine():
        return structural_refinement(
            [(true(), [Update(Variable('cl'), BiOp(Variable('cl'), '+', Value(-1)))])],
            true(),
            exit_condition,
            0,
            set(),
            {'cl': INTEGER},
        )

    target = (
        'analysis.refinement.fairness_refinement.structural_refinement.bdd_simplify'
    )
    with patch(target, return_value=None) as simplify, patch(
        target.replace('bdd_simplify', 'normalise_formula'),
        wraps=normalise_formula,
    ) as normalise:
        actual = refine()

    simplify.assert_called_once()
    assert normalise.call_args_list[1].args[0] is exit_condition
    assert actual[1]
