from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
DIAGONAL_FORMULA = QUANTUM / "DensityOperator" / "DiagonalFormula.lean"
ENTROPY_DIAGONAL = QUANTUM / "Entropy" / "Diagonal.lean"
PURE_POINT = QUANTUM / "LinearResponse" / "PurePointDynamics.lean"

GENERAL_DIAGONAL_DECLARATIONS = (
    "DensityOperator.hasSum_diagonal_weights",
    "DensityOperator.summable_diagonal_weights",
    "DensityOperator.diagonal_weight_le_one",
    "normalizedDiagonalWeight",
    "summable_norm_normalizedDiagonalWeight",
    "diagonalDensityOperator_apply_basis",
    "normalizedDiagonalWeight_nonneg",
    "hasSum_normalizedDiagonalWeight",
    "normalizedDiagonalWeight_le_one",
)

RETIRED_PURE_POINT_DECLARATIONS = (
    "purePointExpectationTerm",
    "summable_purePointExpectationTerm",
    "purePointExpectationValue",
    "purePointExpectationValue_add",
    "purePointExpectationValue_smul",
    "purePointExpectationValue_norm_le",
    "PurePointLehmannData.summable_norm_probability",
    "PurePointLehmannData.probability_tsum_pos",
    "timeScaledGenerator_apply_purePointBasis",
    "pow_timeScaledGenerator_apply_purePointBasis",
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def declaration_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"^\s*(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+"
        rf"{re.escape(name)}\b",
        re.MULTILINE,
    )


def declaration_owners(name: str) -> list[Path]:
    pattern = declaration_pattern(name)
    owners: list[Path] = []
    for path in lean_files(QUANTUM):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if pattern.search(code):
            owners.append(path)
    return owners


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
    entropy_code = strip_lean_comments(ENTROPY_DIAGONAL.read_text(encoding="utf-8"))
    pure_point_code = strip_lean_comments(PURE_POINT.read_text(encoding="utf-8"))

    for declaration in GENERAL_DIAGONAL_DECLARATIONS:
        owners = declaration_owners(declaration)
        if owners != [DIAGONAL_FORMULA]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"general diagonal-state declaration `{declaration}` must be owned exactly once "
                f"by {relative(DIAGONAL_FORMULA)}; found: {rendered}"
            )

    if "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula" not in entropy_code:
        errors.append(
            "entropy diagonal formulas must consume the canonical density diagonal layer in "
            f"{relative(ENTROPY_DIAGONAL)}"
        )

    for declaration in RETIRED_PURE_POINT_DECLARATIONS:
        owners = declaration_owners(declaration)
        if owners:
            rendered = ", ".join(relative(path) for path in owners)
            errors.append(
                f"retired parallel pure-point expectation declaration `{declaration}` found in: "
                f"{rendered}"
            )

    forbidden_pure_point_fragments = (
        "IsBoundedLinearMap.toContinuousLinearMap",
        "toContinuousLinearMap :=",
        "import LeanCondensedMatter.QuantumTheory.Entropy",
        "rw [inner_purePointBasis_heisenbergEvolution system data A i i t]",
    )
    for fragment in forbidden_pure_point_fragments:
        if fragment in pure_point_code:
            errors.append(
                f"pure-point response must not reintroduce `{fragment}` in {relative(PURE_POINT)}"
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
