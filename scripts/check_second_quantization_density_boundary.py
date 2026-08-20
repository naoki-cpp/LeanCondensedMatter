from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
THERMAL = LEAN / "SecondQuantization" / "Common" / "Thermal"
PURE_POINT = LEAN / "QuantumTheory" / "Gibbs" / "PurePoint.lean"
FINITE_HILBERT = THERMAL / "FiniteHilbertOperator.lean"
FINITE_EXPECTATION = THERMAL / "FiniteGibbsExpectationBridge.lean"
FREE_ENTROPY = LEAN / "SecondQuantization" / "Fermionic" / "Thermal" / "FreeEntropy.lean"


def code(path):
    return strip_lean_comments(path.read_text(encoding="utf-8"))


def main() -> int:
    errors: list[str] = []

    for path in (PURE_POINT, FINITE_HILBERT, FINITE_EXPECTATION, FREE_ENTROPY):
        if not path.exists():
            errors.append(f"missing density boundary file: {path.relative_to(ROOT)}")
    for name in ("FiniteGibbsDensityOperator.lean", "PurePointCompatibility.lean"):
        if (THERMAL / name).exists():
            errors.append(f"obsolete finite Gibbs owner remains: {THERMAL.relative_to(ROOT) / name}")

    if errors:
        return finish_audit(errors,
            failure_heading="SecondQuantization density-boundary audit failed:",
            success_message="SecondQuantization density-boundary audit passed.")

    pure = code(PURE_POINT)
    if "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula" not in pure:
        errors.append("PurePoint must import the diagonal density owner directly")
    if "import LeanCondensedMatter.QuantumTheory.Entropy" in pure:
        errors.append("PurePoint must remain independent of entropy")
    for name in ("purePointGibbsDensityOperator", "finitePurePointGibbsDensityOperator"):
        if name not in pure:
            errors.append(f"PurePoint must own `{name}`")

    finite = code(FINITE_HILBERT)
    if any(name in finite for name in ("Gibbs", "Boltzmann", "DensityOperator")):
        errors.append("FiniteHilbertOperator must remain independent of thermal states")

    expectation = code(FINITE_EXPECTATION)
    for required in (
        "import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint",
        "import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteHilbertOperator",
        "finitePurePointGibbsDensityOperator",
    ):
        if required not in expectation:
            errors.append(f"finite Gibbs expectation adapter must use `{required}`")

    entropy = code(FREE_ENTROPY)
    if "import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal" not in entropy:
        errors.append("free-fermion entropy must import the diagonal entropy owner directly")
    if "entropyOpSpectralTraceClass_trace_eq_tsum_diagonal" not in entropy:
        errors.append("free-fermion entropy must retain the diagonal entropy theorem")

    return finish_audit(errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.")


if __name__ == "__main__":
    raise SystemExit(main())
