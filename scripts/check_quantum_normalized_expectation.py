from __future__ import annotations

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
LINEAR_RESPONSE = QUANTUM / "LinearResponse"
EXPECTATION = LINEAR_RESPONSE / "Expectation.lean"
FREE_DYNAMICS = LINEAR_RESPONSE / "FreeDynamics.lean"
STATIONARITY = LINEAR_RESPONSE / "Stationarity.lean"
UNITARY_PERTURBATION = LINEAR_RESPONSE / "UnitaryPerturbation.lean"
EXPECTATION_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation"
FREE_DYNAMICS_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics"


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

    forbidden_expectation_dependencies = (
        "LeanCondensedMatter.Analysis.Dyson",
        "LinearResponse.FreeDynamics",
        "freePropagator",
        "heisenbergEvolution",
        "BoundedFreeSystem",
    )
    for fragment in forbidden_expectation_dependencies:
        if fragment in expectation_code:
            errors.append(
                f"expectation core must remain independent of dynamics via `{fragment}` in "
                f"{EXPECTATION.relative_to(ROOT)}"
            )

    stationarity_imports = lean_imports(STATIONARITY)
    for imported in (EXPECTATION_MODULE, FREE_DYNAMICS_MODULE):
        if imported not in stationarity_imports:
            errors.append(
                f"stationarity layer must import `{imported}` in {STATIONARITY.relative_to(ROOT)}"
            )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory normalized-expectation audit failed:",
        success_message="QuantumTheory normalized-expectation audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
