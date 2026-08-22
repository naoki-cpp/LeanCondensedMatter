from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files_matching,
    lean_imports,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
LEAN_ROOT = ROOT / "LeanCondensedMatter"
QUANTUM = LEAN_ROOT / "QuantumTheory"
PICTURE = QUANTUM / "LinearResponse" / "PictureEquivalence.lean"
UNITARY_TRACE = LEAN_ROOT / "Analysis" / "Operator" / "TraceClass" / "Unitary.lean"
DENSITY_DIAGONAL = QUANTUM / "DensityOperator" / "Diagonal.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
PICTURE_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"
EVOLVE_DENSITY_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+evolveDensityOperator\b", re.MULTILINE
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    required_files = (PICTURE, UNITARY_TRACE, DENSITY_DIAGONAL)
    for path in required_files:
        if not path.exists():
            errors.append(f"missing picture-equivalence boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory picture-equivalence audit failed:",
            success_message="QuantumTheory picture-equivalence audit passed.",
        )

    picture_code = strip_lean_comments(PICTURE.read_text(encoding="utf-8"))
    unitary_code = strip_lean_comments(UNITARY_TRACE.read_text(encoding="utf-8"))
    diagonal_code = strip_lean_comments(DENSITY_DIAGONAL.read_text(encoding="utf-8"))

    required_picture_declarations = (
        "noncomputable def heisenbergObservable",
        "theorem expValue_evolveState_eq_heisenberg",
        "theorem observableExpValue_evolveState_eq_heisenberg",
        "noncomputable def evolveDensityOperator",
        "theorem evolveDensityOperator_isPositive",
        "theorem evolveDensityOperator_trace_eq_one",
        "noncomputable def freePropagatorLinearIsometryEquiv",
        "noncomputable def evolveHilbertBasis",
        "theorem expectation_evolveDensityOperator_eq_heisenberg",
        "theorem observableExpectation_evolveDensityOperator_eq_heisenberg",
    )
    for declaration in required_picture_declarations:
        if declaration not in picture_code:
            errors.append(
                f"missing picture-equivalence declaration `{declaration}` in {relative(PICTURE)}"
            )

    required_unitary_declarations = (
        "noncomputable def unitaryConjugate",
        "theorem eigenspace_unitaryConjugate",
        "theorem finrank_eigenspace_unitaryConjugate",
        "theorem hasSummableRealEigenvalues_unitaryConjugate",
        "theorem spectralTrace_unitaryConjugate",
        "theorem isCompactOperator_unitaryConjugate",
        "theorem IsPositive.unitaryConjugate",
        "theorem SpectralTraceClass.unitaryConjugate",
        "theorem SpectralTraceClass.trace_unitaryConjugate",
    )
    for declaration in required_unitary_declarations:
        if declaration not in unitary_code:
            errors.append(
                f"missing unitary trace-class declaration `{declaration}` in "
                f"{relative(UNITARY_TRACE)}"
            )

    if "theorem DensityOperator.exists_diagonal_hilbertBasis" not in diagonal_code:
        errors.append(
            "density-state picture equivalence requires the canonical diagonal Hilbert-basis "
            f"existence theorem in {relative(DENSITY_DIAGONAL)}"
        )

    if PICTURE_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose Schrödinger-Heisenberg picture equivalence: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    evolve_density_declarations = lean_files_matching(QUANTUM, EVOLVE_DENSITY_DECL)
    if evolve_density_declarations != [PICTURE]:
        rendered = ", ".join(relative(path) for path in evolve_density_declarations) or "<none>"
        errors.append(
            "canonical density-state evolution must be declared exactly once in "
            f"{relative(PICTURE)}; found: {rendered}"
        )

    for path, code in ((PICTURE, picture_code), (UNITARY_TRACE, unitary_code)):
        for finite_assumption in ("[FiniteDimensional", "[Fintype"):
            if finite_assumption in code:
                errors.append(
                    "picture-equivalence foundations must remain dimension-independent; found "
                    f"`{finite_assumption}` in {relative(path)}"
                )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory picture-equivalence audit failed:",
        success_message="QuantumTheory picture-equivalence audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
