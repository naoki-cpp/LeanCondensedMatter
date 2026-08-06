from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
FINITE_GIBBS = (
    ROOT
    / "LeanCondensedMatter"
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "FiniteGibbsDensityOperator.lean"
)
FREE_ENTROPY = (
    ROOT
    / "LeanCondensedMatter"
    / "SecondQuantization"
    / "Fermionic"
    / "Thermal"
    / "FreeEntropy.lean"
)

DENSITY_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
)
ENTROPY_PREFIX = "import LeanCondensedMatter.QuantumTheory.Entropy"
ENTROPY_DIAGONAL_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal"
)


def main() -> int:
    errors: list[str] = []

    if not FINITE_GIBBS.exists():
        errors.append(
            "missing finite Gibbs density boundary file: "
            f"{FINITE_GIBBS.relative_to(ROOT)}"
        )
    else:
        code = strip_lean_comments(FINITE_GIBBS.read_text(encoding="utf-8"))
        relative = FINITE_GIBBS.relative_to(ROOT)

        if DENSITY_IMPORT not in code:
            errors.append(
                "finite Gibbs density construction must import the density diagonal owner "
                f"directly in {relative}"
            )

        if ENTROPY_PREFIX in code:
            errors.append(
                "finite Gibbs density construction must not depend on the entropy layer in "
                f"{relative}"
            )

        for boundary in (
            "diagonalDensityOperator",
            "diagonalDensityOperator_apply_basis",
            "normalizedDiagonalWeight",
        ):
            if boundary not in code:
                errors.append(
                    f"finite Gibbs density construction must retain density API `{boundary}` in "
                    f"{relative}"
                )

    if not FREE_ENTROPY.exists():
        errors.append(
            "missing free-fermion entropy boundary file: "
            f"{FREE_ENTROPY.relative_to(ROOT)}"
        )
    else:
        code = strip_lean_comments(FREE_ENTROPY.read_text(encoding="utf-8"))
        relative = FREE_ENTROPY.relative_to(ROOT)

        if ENTROPY_DIAGONAL_IMPORT not in code:
            errors.append(
                "free-fermion entropy must import the entropy diagonal theorem owner directly in "
                f"{relative}"
            )

        if "entropyOpSpectralTraceClass_trace_eq_tsum_diagonal" not in code:
            errors.append(
                "free-fermion entropy must retain its diagonal entropy theorem use in "
                f"{relative}"
            )

    return finish_audit(
        errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
