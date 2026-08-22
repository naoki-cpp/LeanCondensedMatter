from __future__ import annotations

from architecture_audit_common import (
    finish_audit,
    forbid_import_prefixes,
    lean_imports,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ALGEBRA = LEAN / "SecondQuantization" / "Common" / "Algebra"
THERMAL = LEAN / "SecondQuantization" / "Common" / "Thermal"
PURE_POINT = LEAN / "QuantumTheory" / "Gibbs" / "PurePoint.lean"
FINITE_HILBERT = ALGEBRA / "FiniteHilbertOperator.lean"
FINITE_EXPECTATION = THERMAL / "FiniteGibbsExpectationBridge.lean"
FREE_ENTROPY = LEAN / "SecondQuantization" / "Fermionic" / "Thermal" / "FreeEntropy.lean"

DIAGONAL_FORMULA_MODULE = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
ENTROPY_PREFIX = "LeanCondensedMatter.QuantumTheory.Entropy"
PURE_POINT_MODULE = "LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint"
FINITE_HILBERT_MODULE = "LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator"
ENTROPY_DIAGONAL_MODULE = "LeanCondensedMatter.QuantumTheory.Entropy.Diagonal"


def code(path):
    return strip_lean_comments(path.read_text(encoding="utf-8"))


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

    pure = code(PURE_POINT)
    pure_imports = lean_imports(PURE_POINT)
    if DIAGONAL_FORMULA_MODULE not in pure_imports:
        errors.append("PurePoint must import the diagonal density owner directly")
    forbid_import_prefixes(
        errors,
        PURE_POINT,
        ENTROPY_PREFIX,
        root=ROOT,
        description="PurePoint must remain independent of entropy",
    )
    for name in ("purePointGibbsDensityOperator", "finitePurePointGibbsDensityOperator"):
        if name not in pure:
            errors.append(f"PurePoint must own `{name}`")

    finite = code(FINITE_HILBERT)
    if any(name in finite for name in ("Gibbs", "Boltzmann", "DensityOperator")):
        errors.append("FiniteHilbertOperator must remain independent of thermal states")

    expectation = code(FINITE_EXPECTATION)
    expectation_imports = lean_imports(FINITE_EXPECTATION)
    for required in (PURE_POINT_MODULE, FINITE_HILBERT_MODULE):
        if required not in expectation_imports:
            errors.append(f"finite Gibbs expectation adapter must import `{required}`")
    if "finitePurePointGibbsDensityOperator" not in expectation:
        errors.append(
            "finite Gibbs expectation adapter must consume `finitePurePointGibbsDensityOperator`"
        )

    entropy = code(FREE_ENTROPY)
    if ENTROPY_DIAGONAL_MODULE not in lean_imports(FREE_ENTROPY):
        errors.append("free-fermion entropy must import the diagonal entropy owner directly")
    if "entropyOpSpectralTraceClass_trace_eq_tsum_diagonal" not in entropy:
        errors.append("free-fermion entropy must expose the diagonal entropy theorem")

    return finish_audit(
        errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
