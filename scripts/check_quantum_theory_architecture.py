from __future__ import annotations

import re
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

PROBABILITY_KERNEL_DEF = re.compile(
    r"\bprivate\s+noncomputable\s+def\s+probabilityKernel\b"
    r"(?P<body>.*?)"
    r"(?=\n\s*private\s+theorem\s+probabilityKernel_nonneg\b)",
    re.DOTALL,
)

EXPECTED_BORN = QUANTUM / "POVM" / "Born.lean"
DENSITY_UMBRELLA = QUANTUM / "DensityOperator.lean"
COUNTABLE_DIAGONAL_BRIDGE = QUANTUM / "DensityOperator" / "DiagonalExpectation.lean"
COUNTABLE_DIAGONAL_FORMULA = QUANTUM / "DensityOperator" / "DiagonalFormula.lean"

COUNTABLE_BRIDGE_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation"
COUNTABLE_FORMULA_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_born_probability_boundary(errors: list[str]) -> None:
    born_code = strip_lean_comments(EXPECTED_BORN.read_text(encoding="utf-8"))
    kernel_match = PROBABILITY_KERNEL_DEF.search(born_code)
    if kernel_match is None:
        errors.append(f"missing canonical Born probability kernel in {relative(EXPECTED_BORN)}")
        return

    kernel_body = kernel_match.group("body")
    if "diagonalExpectationValue" not in kernel_body:
        errors.append(
            "Born probability kernel must use lossless diagonalExpectationValue in "
            f"{relative(EXPECTED_BORN)}"
        )
    if ".re" in kernel_body:
        errors.append(
            "Born probability kernel must not define a physical real value by direct .re in "
            f"{relative(EXPECTED_BORN)}"
        )


def check_countable_diagonal_boundary(errors: list[str]) -> None:
    bridge_code = strip_lean_comments(COUNTABLE_DIAGONAL_BRIDGE.read_text(encoding="utf-8"))
    formula_code = strip_lean_comments(COUNTABLE_DIAGONAL_FORMULA.read_text(encoding="utf-8"))

    for path, code in (
        (COUNTABLE_DIAGONAL_BRIDGE, bridge_code),
        (COUNTABLE_DIAGONAL_FORMULA, formula_code),
    ):
        if "[FiniteDimensional" in code:
            errors.append(
                "generic countable diagonal module has a finite-dimensional assumption: "
                f"{relative(path)}"
            )
        if "[Fintype" in code:
            errors.append(
                f"generic countable diagonal module has a finite-index assumption: {relative(path)}"
            )

    umbrella_imports = lean_imports(DENSITY_UMBRELLA)
    if COUNTABLE_BRIDGE_IMPORT not in umbrella_imports:
        errors.append(
            "density-state umbrella must import the Hilbert-Schmidt diagonal bridge: "
            f"{relative(DENSITY_UMBRELLA)}"
        )
    if COUNTABLE_FORMULA_IMPORT not in umbrella_imports:
        errors.append(
            "density-state umbrella must import the countable diagonal formulas: "
            f"{relative(DENSITY_UMBRELLA)}"
        )


def main() -> int:
    errors: list[str] = []

    check_born_probability_boundary(errors)
    check_countable_diagonal_boundary(errors)

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
