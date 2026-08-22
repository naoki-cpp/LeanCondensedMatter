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
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"

DENSITY_DECL = re.compile(r"^\s*structure\s+DensityOperator\b", re.MULTILINE)
POVM_DECL = re.compile(r"^\s*structure\s+POVM\b", re.MULTILINE)
PURE_REAL_EXPECTATION_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+observableExpValue\b", re.MULTILINE
)
DENSITY_REAL_EXPECTATION_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+DensityOperator\.observableExpectation\b", re.MULTILINE
)
PROB_NNREAL_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+probNNReal\b", re.MULTILINE
)
BORN_PMF_DECL = re.compile(
    r"^\s*noncomputable\s+def\s+bornPMF\b", re.MULTILINE
)
PROBABILITY_KERNEL_DEF = re.compile(
    r"\bprivate\s+noncomputable\s+def\s+probabilityKernel\b"
    r"(?P<body>.*?)"
    r"(?=\n\s*private\s+theorem\s+probabilityKernel_nonneg\b)",
    re.DOTALL,
)

EXPECTED_DENSITY = QUANTUM / "DensityOperator" / "Basic.lean"
EXPECTED_POVM = QUANTUM / "POVM" / "Basic.lean"
EXPECTED_PURE_REAL_EXPECTATION = QUANTUM / "Postulates.lean"
EXPECTED_DENSITY_REAL_EXPECTATION = QUANTUM / "DensityOperator" / "ObservableExpectation.lean"
EXPECTED_BORN = QUANTUM / "POVM" / "Born.lean"
DENSITY_UMBRELLA = QUANTUM / "DensityOperator.lean"
COUNTABLE_DIAGONAL_BRIDGE = QUANTUM / "DensityOperator" / "DiagonalExpectation.lean"
COUNTABLE_DIAGONAL_FORMULA = QUANTUM / "DensityOperator" / "DiagonalFormula.lean"
GIBBS_DIAGONAL_ENERGY = QUANTUM / "Gibbs" / "DiagonalEnergy.lean"

COUNTABLE_BRIDGE_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation"
COUNTABLE_FORMULA_IMPORT = "LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def require_unique_owner(
    errors: list[str], pattern: re.Pattern[str], owner: Path, description: str
) -> None:
    owners = lean_files_matching(QUANTUM, pattern)
    if owners != [owner]:
        rendered = ", ".join(relative(path) for path in owners) or "<none>"
        errors.append(
            f"{description} must be declared exactly once in {relative(owner)}; found: {rendered}"
        )


def check_observable_expectation_boundary(errors: list[str]) -> None:
    require_unique_owner(
        errors,
        PURE_REAL_EXPECTATION_DECL,
        EXPECTED_PURE_REAL_EXPECTATION,
        "canonical pure-state real observable expectation",
    )
    require_unique_owner(
        errors,
        DENSITY_REAL_EXPECTATION_DECL,
        EXPECTED_DENSITY_REAL_EXPECTATION,
        "canonical density-state real observable expectation",
    )


def check_born_probability_boundary(errors: list[str]) -> None:
    require_unique_owner(
        errors,
        PROB_NNREAL_DECL,
        EXPECTED_BORN,
        "canonical nonnegative Born probability",
    )
    require_unique_owner(
        errors,
        BORN_PMF_DECL,
        EXPECTED_BORN,
        "canonical Born probability mass function",
    )

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
    energy_code = strip_lean_comments(GIBBS_DIAGONAL_ENERGY.read_text(encoding="utf-8"))

    required_bridge = (
        "noncomputable def DensityOperator.sqrtOp",
        "theorem DensityOperator.sqrtOp_isHilbertSchmidt",
        "theorem DensityOperator.expectation_eq_innerHS",
    )
    for declaration in required_bridge:
        if declaration not in bridge_code:
            errors.append(
                f"missing countable diagonal bridge `{declaration}` in "
                f"{relative(COUNTABLE_DIAGONAL_BRIDGE)}"
            )

    required_formula = (
        "theorem DensityOperator.hasSum_expectation_diagonal",
        "theorem DensityOperator.summable_expectation_diagonal",
        "theorem DensityOperator.expectation_eq_tsum_diagonal",
        "theorem DensityOperator.observableExpectation_eq_tsum_diagonal",
    )
    for declaration in required_formula:
        if declaration not in formula_code:
            errors.append(
                f"missing countable diagonal formula `{declaration}` in "
                f"{relative(COUNTABLE_DIAGONAL_FORMULA)}"
            )

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

    if "theorem energyExpValue_eq_tsum_common_eigenbasis" not in energy_code:
        errors.append(
            "Gibbs diagonal energy must expose the HilbertBasis/tsum foundation in "
            f"{relative(GIBBS_DIAGONAL_ENERGY)}"
        )


def main() -> int:
    errors: list[str] = []

    require_unique_owner(errors, DENSITY_DECL, EXPECTED_DENSITY, "canonical DensityOperator")
    require_unique_owner(errors, POVM_DECL, EXPECTED_POVM, "canonical POVM")
    check_observable_expectation_boundary(errors)
    check_born_probability_boundary(errors)
    check_countable_diagonal_boundary(errors)

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
