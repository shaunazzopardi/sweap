from types import SimpleNamespace

import pytest
from analysis.abstraction.concretisation import concretize_transitions
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.util import conjunct, iff, is_tautology, neg, true
from prop_lang.value import Value
from prop_lang.variable import Variable


@pytest.mark.parametrize("with_prefix", [False, True])
def test_state_mismatch_preserves_prefix_and_extracts_failed_guard(with_prefix):
    request, x = Variable("request"), Variable("x")
    positive = BiOp(x, ">", Value(0))
    enter = Transition("s0", true(), [], [], "s1")
    guarded = Transition("s1", conjunct(request, positive), [], [], "s2")
    program = SimpleNamespace(
        transitions=[enter, guarded],
        deterministic=True,
        env_events=[(request, BOOLEAN)],
        con_events=[],
        symbol_table={"request": BOOLEAN, "x": INTEGER},
        inp_out_puts=[request],
        states=["s0", "s1", "s2"],
    )
    # At x=0 the abstraction's requested s1 -> s2 step cannot occur.
    # The preceding s0 -> s1 step, when present, remains agreed upon.
    states = [
        {"s0": "TRUE", "s1": "FALSE", "s2": "FALSE", "x": "0"},
        {"s0": "FALSE", "s1": "TRUE", "s2": "FALSE", "x": "0"},
    ]
    choices = [
        {"request": "FALSE", "compatible_states": "TRUE"},
        {"request": "TRUE", "compatible_states": "TRUE"},
    ]
    indices = ["0", "1"]
    if not with_prefix:
        indices, states, choices = indices[1:], states[1:], choices[1:]
    mismatch = ("1", states[-1], {"request": "FALSE", "compatible_states": "FALSE"})
    agreed, (wanted, failed) = concretize_transitions(
        program, (indices, states, choices), mismatch
    )
    assert agreed == ([(enter, states[0], choices[0])] if with_prefix else [])
    assert failed == (guarded, states[-1], choices[-1])
    # Substitute events from the failed transition's source, not the mismatch
    # state's following input; preserve the data predicate for refinement.
    assert len(wanted) == 1
    assert set(wanted[0].variablesin()) == {x}
    assert is_tautology(iff(wanted[0], neg(positive)), program.symbol_table)
