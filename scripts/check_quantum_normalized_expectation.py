from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
FREE_DYNAMICS = (
    ROOT
    / "LeanCondensedMatter"
    / "QuantumTheory"
    / "LinearResponse"
    / "FreeDynamics.lean"
)
UNITARY_PERTURBATION = (
    ROOT
    / "LeanCondensedMatter"
    / "QuantumTheory"
    / "LinearResponse"
    / "UnitaryPerturbation.lean"
)


def main() -> int:
    errors: list[str] = []

    for path in (FREE_DYNAMICS, UNITARY_PERTURBATION):
        if not path.exists():
            errors.append(f"missing normalized-expectation boundary file: {path.relative_to(ROOT)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory normalized-expectation audit failed:",
            success_message="QuantumTheory normalized-expectation audit passed.",
        )

    free_code = strip_lean_comments(FREE_DYNAMICS.read_text(encoding="utf-8"))
    unitary_code = strip_lean_comments(UNITARY_PERTURBATION.read_text(encoding="utf-8"))
    free_normalized = " ".join(free_code.split())
    unitary_normalized = " ".join(unitary_code.split())

    required_free_fragments = (
        "noncomputable def NormalizedExpectation.pullback",
        "expectation.toContinuousLinearMap.comp Φ",
        "theorem NormalizedExpectation.pullback_apply",
    )
    for fragment in required_free_fragments:
        if fragment not in free_normalized:
            errors.append(
                f"missing canonical normalized-expectation fragment `{fragment}` in "
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
