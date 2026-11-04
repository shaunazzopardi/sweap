"""Verdicts must follow the verification and candidate-refinement policies."""

from types import SimpleNamespace
from unittest.mock import Mock

import pytest

from config import Config
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from synthesis import synthesis as synthesis_module


@pytest.fixture
def synthesis_loop(monkeypatch, tmp_path):
    conf = Config.getConfig()
    monkeypatch.setattr(conf, "finite_synthesis", False)
    program = SimpleNamespace(
        deterministic=True,
        env_events=[],
        con_events=[],
        out_events=[],
        to_prog=lambda _formula: "program {}",
    )
    abstraction = SimpleNamespace(
        raw_state_predicates=set(),
        raw_transition_predicates=set(),
        symbol_table={},
    )
    problem = SimpleNamespace(tlsf="INFO { }", init_choice_logic=None)
    verdict = SimpleNamespace(realisable=True, machine=object())
    assumption, guarantee = Variable("assumption"), Variable("guarantee")
    original_ltl = Variable("original_specification")
    signatures = {"initial-signature"}
    refinement = Mock(return_value=(True, verdict.machine))
    verification = Mock()

    # Isolate solvers, abstraction construction, and logging; exercise the real
    # loop's acceptance, refinement, and verification decisions.
    monkeypatch.setattr(
        synthesis_module,
        "extract_init_preds",
        Mock(
            return_value=(set(), [assumption], [guarantee], signatures, {}),
        ),
    )
    monkeypatch.setattr(
        synthesis_module, "EffectsAbstraction", Mock(return_value=abstraction)
    )
    monkeypatch.setattr(
        synthesis_module,
        "refining_abs_and_log",
        Mock(
            return_value=(abstraction, problem),
        ),
    )
    monkeypatch.setattr(
        synthesis_module.ltl_synthesis, "ltl_synthesis", Mock(return_value=verdict)
    )
    monkeypatch.setattr(synthesis_module, "refinement_standard", refinement)
    monkeypatch.setattr(synthesis_module, "verify_strategy", verification)
    monkeypatch.setattr(
        synthesis_module,
        "generate_tlsf_file_name_template",
        lambda: str(tmp_path / "synthesis"),
    )
    for name in (
        "safe_overwrite_if_logging",
        "safe_rename_logging",
        "print_binary_rep_tables_at_end",
    ):
        monkeypatch.setattr(synthesis_module, name, Mock())

    def run():
        return synthesis_module.abstract_synthesis_loop(
            program,
            [assumption],
            [guarantee],
            original_ltl,
            [],
            [],
            bound=1,
        )

    return SimpleNamespace(
        run=run,
        program=program,
        abstraction=abstraction,
        problem=problem,
        verdict=verdict,
        assumption=assumption,
        guarantee=guarantee,
        original_ltl=original_ltl,
        signatures=signatures,
        refinement=refinement,
        verification=verification,
    )


@pytest.mark.parametrize("dual", [False, True], ids=["base", "dual"])
@pytest.mark.parametrize("realisable", [False, True], ids=["negative", "positive"])
@pytest.mark.parametrize(
    "verify", [False, True], ids=["verification-off", "verification-on"]
)
def test_verification_uses_requested_polarity_and_context(
    synthesis_loop, monkeypatch, dual, realisable, verify
):
    loop = synthesis_loop
    monkeypatch.setattr(Config.getConfig(), "dual", dual)
    monkeypatch.setattr(Config.getConfig(), "verify_controller", verify)
    loop.verdict.realisable = realisable

    assert loop.run() is loop.verdict
    if not verify:
        loop.verification.assert_not_called()
        return

    # The dual loop must use the original specification, whereas the base loop
    # uses its assumption/guarantee contract. They deliberately differ here.
    expected = (
        loop.original_ltl if dual else BiOp(loop.assumption, "->", loop.guarantee)
    )
    if not realisable:
        expected = UniOp("!", expected)
    loop.verification.assert_called_once_with(
        loop.program,
        loop.abstraction,
        loop.verdict.machine,
        expected,
        loop.problem,
    )
    args = loop.verification.call_args.args
    assert args[0] is loop.program
    assert args[1] is loop.abstraction
    assert args[2] is loop.verdict.machine
    assert args[4] is loop.problem


@pytest.mark.parametrize("dual", [False, True], ids=["base", "dual"])
@pytest.mark.parametrize(
    "compatible", [False, True], ids=["incompatible", "compatible"]
)
def test_candidate_requires_compatibility_before_acceptance(
    synthesis_loop, monkeypatch, dual, compatible
):
    loop = synthesis_loop
    monkeypatch.setattr(Config.getConfig(), "dual", dual)
    monkeypatch.setattr(Config.getConfig(), "verify_controller", False)
    # The negative base verdict and positive dual verdict are candidates that
    # need a compatibility check before they can be accepted.
    loop.verdict.realisable = dual
    if compatible:
        assert loop.run() is loop.verdict
    else:
        loop.refinement.return_value = (
            False,
            (({Variable("new_predicate")}, set()), [], [], [], 1),
        )
        with pytest.raises(
            Exception,
            match="Could not find a controller or counterstrategy with 1 iterations",
        ):
            loop.run()

    loop.refinement.assert_called_once_with(
        loop.program,
        loop.abstraction,
        loop.verdict.machine,
        dual,
        loop.signatures,
        0,
        loop.problem,
        False,
    )
    loop.verification.assert_not_called()
