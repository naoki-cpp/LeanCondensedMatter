from __future__ import annotations

from architecture_audit_common import finish_audit, lean_imports, repository_root

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ALGEBRA = LEAN / "SecondQuantization" / "Common" / "Algebra"
THERMAL = LEAN / "SecondQuantization" / "Common" / "Thermal"
PURE_POINT = LEAN / "QuantumTheory" / "Gibbs" / "PurePoint.lean"
FINITE_HILBERT = ALGEBRA / "FiniteHilbertOperator.lean"
FINITE_EXPECTATION = THERMAL / "FiniteGibbsExpectationBridge.lean"
FREE_ENTROPY = LEAN / "SecondQuantization" / "Fermionic" / "Thermal" / "FreeEntropy.lean"

DIAGONAL_FORMULA_MODULE = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
PURE_POINT_MODULE = "LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint"
FINITE_HILBERT_MODULE = "LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator"
ENTROPY_DIAGONAL_MODULE = "LeanCondensedMatter.QuantumTheory.Entropy.Diagonal"


def main() -> int:
    errors: list[str] = []

    for path in (PURE_POINT, FINITE_HILBERT, FINITE_EXPECTATION, FREE_ENTROPY):
        if not path.exists():
            errors.append(f"missing density boundary file: {path.relative_to(ROOT)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="SecondQuantization density-boundary audit failed:",
            success_message="SecondQuantization density-boundary audit passed.",
        )

    # Semantic owners and public type-layer independence are compiled Lean contracts.
    if DIAGONAL_FORMULA_MODULE not in lean_imports(PURE_POINT):
        errors.append("PurePoint must import the diagonal density owner directly")

    expectation_imports = lean_imports(FINITE_EXPECTATION)
    for required in (PURE_POINT_MODULE, FINITE_HILBERT_MODULE):
        if required not in expectation_imports:
            errors.append(f"finite Gibbs expectation adapter must import `{required}`")

    if ENTROPY_DIAGONAL_MODULE not in lean_imports(FREE_ENTROPY):
        errors.append("free-fermion entropy must import the diagonal entropy owner directly")

    return finish_audit(
        errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
