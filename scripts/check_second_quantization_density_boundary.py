from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
PURE_POINT = LEAN / "QuantumTheory" / "Gibbs" / "PurePoint.lean"
FINITE_HILBERT = (
    LEAN
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "FiniteHilbertOperator.lean"
)
FINITE_EXPECTATION = (
    LEAN
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "FiniteGibbsExpectationBridge.lean"
)
FREE_ENTROPY = (
    LEAN
    / "SecondQuantization"
    / "Fermionic"
    / "Thermal"
    / "FreeEntropy.lean"
)
OBSOLETE_FINITE_GIBBS = (
    LEAN
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "FiniteGibbsDensityOperator.lean"
)
OBSOLETE_PURE_POINT_COMPATIBILITY = (
    LEAN
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "PurePointCompatibility.lean"
)

DENSITY_IMPORT = "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
PURE_POINT_IMPORT = "import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint"
FINITE_HILBERT_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator"
)
ENTROPY_PREFIX = "import LeanCondensedMatter.QuantumTheory.Entropy"
ENTROPY_DIAGONAL_IMPORT = "import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal"


def main() -> int:
    errors: list[str] = []

    for path, description in (
        (PURE_POINT, "generic pure-point Gibbs owner"),
        (FINITE_HILBERT, "finite Hilbert transport owner"),
        (FINITE_EXPECTATION, "finite Gibbs expectation adapter"),
        (FREE_ENTROPY, "free-fermion entropy boundary"),
    ):
        if not path.exists():
            errors.append(f"missing {description}: {path.relative_to(ROOT)}")

    for path in (OBSOLETE_FINITE_GIBBS, OBSOLETE_PURE_POINT_COMPATIBILITY):
        if path.exists():
            errors.append(f"obsolete finite Gibbs compatibility owner remains: {path.relative_to(ROOT)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="SecondQuantization density-boundary audit failed:",
            success_message="SecondQuantization density-boundary audit passed.",
        )

    pure_point_code = strip_lean_comments(PURE_POINT.read_text(encoding="utf-8"))
    pure_point_relative = PURE_POINT.relative_to(ROOT)
    if DENSITY_IMPORT not in pure_point_code:
        errors.append(
            "generic pure-point Gibbs construction must import the diagonal density owner directly "
            f"in {pure_point_relative}"
        )
    if ENTROPY_PREFIX in pure_point_code:
        errors.append(
            "generic pure-point Gibbs construction must not depend on the entropy layer in "
            f"{pure_point_relative}"
        )
    for boundary in (
        "purePointBoltzmannWeight",
        "purePointPartitionFunction",
        "purePointGibbsDensityOperator",
        "finitePurePointGibbsDensityOperator",
    ):
        if boundary not in pure_point_code:
            errors.append(
                f"generic pure-point Gibbs owner must retain `{boundary}` in {pure_point_relative}"
            )

    finite_hilbert_code = strip_lean_comments(FINITE_HILBERT.read_text(encoding="utf-8"))
    finite_hilbert_relative = FINITE_HILBERT.relative_to(ROOT)
    for forbidden in ("Gibbs", "Boltzmann", "DensityOperator"):
        if forbidden in finite_hilbert_code:
            errors.append(
                f"finite Hilbert transport must remain thermal-state independent: found `{forbidden}` "
                f"in {finite_hilbert_relative}"
            )

    finite_expectation_code = strip_lean_comments(FINITE_EXPECTATION.read_text(encoding="utf-8"))
    finite_expectation_relative = FINITE_EXPECTATION.relative_to(ROOT)
    for required_import in (PURE_POINT_IMPORT, FINITE_HILBERT_IMPORT):
        if required_import not in finite_expectation_code:
            errors.append(
                f"finite Gibbs expectation adapter must import canonical owner `{required_import}` "
                f"in {finite_expectation_relative}"
            )
    if "finitePurePointGibbsDensityOperator" not in finite_expectation_code:
        errors.append(
            "finite Gibbs expectation adapter must specialize the generic finite pure-point state in "
            f"{finite_expectation_relative}"
        )
    for obsolete in (
        "finiteBoltzmannWeight",
        "finitePartitionFunction",
        "finiteGibbsDensityOperator",
        "diagonalDensityOperator",
    ):
        if obsolete in finite_expectation_code:
            errors.append(
                f"finite Gibbs expectation adapter must not recreate obsolete state API `{obsolete}` "
                f"in {finite_expectation_relative}"
            )

    free_entropy_code = strip_lean_comments(FREE_ENTROPY.read_text(encoding="utf-8"))
    free_entropy_relative = FREE_ENTROPY.relative_to(ROOT)
    if ENTROPY_DIAGONAL_IMPORT not in free_entropy_code:
        errors.append(
            "free-fermion entropy must import the entropy diagonal theorem owner directly in "
            f"{free_entropy_relative}"
        )
    if "entropyOpSpectralTraceClass_trace_eq_tsum_diagonal" not in free_entropy_code:
        errors.append(
            "free-fermion entropy must retain its diagonal entropy theorem use in "
            f"{free_entropy_relative}"
        )

    return finish_audit(
        errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
