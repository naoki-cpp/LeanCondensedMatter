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

DENSITY_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
)
ENTROPY_IMPORT = "import LeanCondensedMatter.QuantumTheory.Entropy"


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

        if ENTROPY_IMPORT in code:
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

    return finish_audit(
        errors,
        failure_heading="SecondQuantization density-boundary audit failed:",
        success_message="SecondQuantization density-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
