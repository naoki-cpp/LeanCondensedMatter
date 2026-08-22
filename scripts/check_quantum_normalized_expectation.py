from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files_matching,
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

NORMALIZED_EXPECTATION_DECL = re.compile(
    r"^\s*structure\s+NormalizedExpectation\b", re.MULTILINE
)


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
    stationarity_code = strip_lean_comments(STATIONARITY.read_text(encoding="utf-8"))
    unitary_code = strip_lean_comments(UNITARY_PERTURBATION.read_text(encoding="utf-8"))

    required_expectation_api = (
        "structure NormalizedExpectation",
        "noncomputable def NormalizedExpectation.pullback",
        "theorem NormalizedExpectation.pullback_apply",
    )
    for declaration in required_expectation_api:
        if declaration not in expectation_code:
            errors.append(
                f"missing normalized-expectation API `{declaration}` in {EXPECTATION.relative_to(ROOT)}"
            )

    owners = lean_files_matching(QUANTUM, NORMALIZED_EXPECTATION_DECL)
    if owners != [EXPECTATION]:
        rendered = ", ".join(str(path.relative_to(ROOT)) for path in owners) or "<none>"
        errors.append(
            "NormalizedExpectation must be owned exactly once by "
            f"{EXPECTATION.relative_to(ROOT)}; found: {rendered}"
        )

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
    for declaration in ("def IsStationary", "theorem expectation_heisenbergEvolution_zero"):
        if declaration not in stationarity_code:
            errors.append(
                f"missing stationarity API `{declaration}` in {STATIONARITY.relative_to(ROOT)}"
            )

    if "theorem timeDependentPerturbedObservableMap_one_of_isSelfAdjoint" not in unitary_code:
        errors.append(
            "finite-coupling dynamics must expose the self-adjoint normalized-expectation bridge in "
            f"{UNITARY_PERTURBATION.relative_to(ROOT)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory normalized-expectation audit failed:",
        success_message="QuantumTheory normalized-expectation audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
