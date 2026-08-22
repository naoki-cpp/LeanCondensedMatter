from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
DIAGONAL_FORMULA = QUANTUM / "DensityOperator" / "DiagonalFormula.lean"
ENTROPY_DIAGONAL = QUANTUM / "Entropy" / "Diagonal.lean"
PURE_POINT = QUANTUM / "LinearResponse" / "PurePointDynamics.lean"
DIAGONAL_MODULE = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    for path in (DIAGONAL_FORMULA, ENTROPY_DIAGONAL, PURE_POINT):
        if not path.exists():
            errors.append(f"missing pure-point density boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory pure-point density audit failed:",
            success_message="QuantumTheory pure-point density audit passed.",
        )

    diagonal_code = strip_lean_comments(DIAGONAL_FORMULA.read_text(encoding="utf-8"))
    pure_point_code = strip_lean_comments(PURE_POINT.read_text(encoding="utf-8"))

    if DIAGONAL_MODULE not in lean_imports(ENTROPY_DIAGONAL):
        errors.append(
            "entropy diagonal formulas must consume the canonical density diagonal layer in "
            f"{relative(ENTROPY_DIAGONAL)}"
        )

    if DIAGONAL_MODULE not in lean_imports(PURE_POINT):
        errors.append(
            "pure-point response must consume the canonical density diagonal layer in "
            f"{relative(PURE_POINT)}"
        )
    for declaration in ("diagonalDensityOperator", ".toNormalizedExpectation"):
        if declaration not in pure_point_code:
            errors.append(
                f"pure-point response must consume canonical density API `{declaration}` in "
                f"{relative(PURE_POINT)}"
            )

    if "entropyOp" in diagonal_code:
        errors.append(
            "density diagonal formulas must not depend on entropy implementation details in "
            f"{relative(DIAGONAL_FORMULA)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory pure-point density audit failed:",
        success_message="QuantumTheory pure-point density audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
