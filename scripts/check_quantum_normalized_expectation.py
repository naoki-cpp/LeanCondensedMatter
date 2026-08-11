from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
LINEAR_RESPONSE = ROOT / "LeanCondensedMatter" / "QuantumTheory" / "LinearResponse"
EXPECTATION = LINEAR_RESPONSE / "Expectation.lean"
FREE_DYNAMICS = LINEAR_RESPONSE / "FreeDynamics.lean"
STATIONARITY = LINEAR_RESPONSE / "Stationarity.lean"
UNITARY_PERTURBATION = LINEAR_RESPONSE / "UnitaryPerturbation.lean"


def main() -> int:
    errors: list[str] = []

    for path in (EXPECTATION, FREE_DYNAMICS, STATIONARITY, UNITARY_PERTURBATION):
        if not path.exists():
            errors.append(f"missing normalized-expectation boundary file: {path.relative_to(ROOT)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory normalized-expectation audit failed:",
            success_message="QuantumTheory normalized-expectation audit passed.",
        )

    expectation_code = strip_lean_comments(EXPECTATION.read_text(encoding="utf-8"))
    free_code = strip_lean_comments(FREE_DYNAMICS.read_text(encoding="utf-8"))
    stationarity_code = strip_lean_comments(STATIONARITY.read_text(encoding="utf-8"))
    unitary_code = strip_lean_comments(UNITARY_PERTURBATION.read_text(encoding="utf-8"))

    expectation_normalized = " ".join(expectation_code.split())
    stationarity_normalized = " ".join(stationarity_code.split())
    unitary_normalized = " ".join(unitary_code.split())

    required_expectation_fragments = (
        "structure NormalizedExpectation",
        "noncomputable def NormalizedExpectation.pullback",
        "expectation.toContinuousLinearMap.comp Φ",
        "theorem NormalizedExpectation.pullback_apply",
    )
    for fragment in required_expectation_fragments:
        if fragment not in expectation_normalized:
            errors.append(
                f"missing canonical normalized-expectation fragment `{fragment}` in "
                f"{EXPECTATION.relative_to(ROOT)}"
            )

    forbidden_expectation_fragments = (
        "LeanCondensedMatter.Analysis.Dyson",
        "LinearResponse.FreeDynamics",
        "freePropagator",
        "heisenbergEvolution",
        "BoundedFreeSystem",
    )
    for fragment in forbidden_expectation_fragments:
        if fragment in expectation_code:
            errors.append(
                f"expectation core must remain independent of dynamics via `{fragment}` in "
                f"{EXPECTATION.relative_to(ROOT)}"
            )

    required_stationarity_fragments = (
        "import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation",
        "import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics",
        "def IsStationary",
        "theorem expectation_heisenbergEvolution_zero",
    )
    for fragment in required_stationarity_fragments:
        if fragment not in stationarity_normalized:
            errors.append(
                f"missing canonical stationarity fragment `{fragment}` in "
                f"{STATIONARITY.relative_to(ROOT)}"
            )

    forbidden_free_fragments = (
        "structure NormalizedExpectation",
        "def NormalizedExpectation.pullback",
        "def IsStationary",
        "theorem expectation_heisenbergEvolution_zero",
    )
    for fragment in forbidden_free_fragments:
        if fragment in free_code:
            errors.append(
                f"free dynamics must not own expectation/stationarity API via `{fragment}` in "
                f"{FREE_DYNAMICS.relative_to(ROOT)}"
            )

    required_unitary_fragments = (
        "theorem timeDependentPerturbedObservableMap_one_of_isSelfAdjoint",
        "expectation.pullback (timeDependentPerturbedObservableMap system V lam t)",
    )
    for fragment in required_unitary_fragments:
        if fragment not in unitary_normalized:
            errors.append(
                f"finite-coupling expectations must retain `{fragment}` in "
                f"{UNITARY_PERTURBATION.relative_to(ROOT)}"
            )

    forbidden_unitary_fragments = (
        ": NormalizedExpectation H where",
        "toContinuousLinearMap :=",
        "map_one :=",
    )
    for fragment in forbidden_unitary_fragments:
        if fragment in unitary_code:
            errors.append(
                f"finite-coupling expectations must not reconstruct the interface via `{fragment}` "
                f"in {UNITARY_PERTURBATION.relative_to(ROOT)}"
            )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory normalized-expectation audit failed:",
        success_message="QuantumTheory normalized-expectation audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
