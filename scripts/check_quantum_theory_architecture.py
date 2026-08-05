from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    check_absent_paths,
    finish_audit,
    lean_files,
    numbered_lines,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
LEAN_ROOT = ROOT / "LeanCondensedMatter"
NOTES = ROOT / "notes"
DOCS = ROOT / "docs"

TRACECLASS_NAMESPACE = re.compile(r"\bQuantumTheory\.TraceClass\b")
TRACECLASS_QUANTUM_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.QuantumTheory\.[A-Za-z0-9_.]*TraceClass(?:\s|$)"
)
LEGACY_QUANTUM_MODULE = re.compile(
    r"(?:LeanCondensedMatter/)?QuantumTheory/[A-Za-z0-9_./-]*TraceClass\.lean"
)
DENSITY_DECL = re.compile(r"^\s*structure\s+DensityOperator\b", re.MULTILINE)
POVM_DECL = re.compile(r"^\s*structure\s+POVM\b", re.MULTILINE)
LEGACY_ALIAS = re.compile(
    r"^\s*(?:abbrev|def)\s+(?:QuantumTheory\.)?TraceClass\.(?:DensityOperator|POVM)\b",
    re.MULTILINE,
)
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
LEGACY_ENERGY_SELF_ADJOINT = re.compile(r"\benergyExpectationSelfAdjoint\b")

EXPECTED_DENSITY = QUANTUM / "DensityOperator" / "Basic.lean"
EXPECTED_POVM = QUANTUM / "POVM" / "Basic.lean"
EXPECTED_PURE_REAL_EXPECTATION = QUANTUM / "Postulates.lean"
EXPECTED_DENSITY_REAL_EXPECTATION = (
    QUANTUM / "DensityOperator" / "ObservableExpectation.lean"
)
EXPECTED_BORN = QUANTUM / "POVM" / "Born.lean"
DENSITY_UMBRELLA = QUANTUM / "DensityOperator.lean"
COUNTABLE_DIAGONAL_BRIDGE = (
    QUANTUM / "DensityOperator" / "DiagonalExpectation.lean"
)
COUNTABLE_DIAGONAL_FORMULA = QUANTUM / "DensityOperator" / "DiagonalFormula.lean"
GIBBS_ENERGY_EXPECTATION = QUANTUM / "Gibbs" / "EnergyExpectation.lean"
GIBBS_DIAGONAL_ENERGY = QUANTUM / "Gibbs" / "DiagonalEnergy.lean"
REMOVED_DOCUMENTS = (
    NOTES / "migrations" / "canonical-quantum-density-theory.md",
)

CANONICAL_PURE_EXPECTATION_BODY = (
    "noncomputable def expValue : ℂ := inner ℂ ψ.1 (A.1 ψ.1)"
)
LEGACY_REVERSED_PURE_EXPECTATION_BODY = (
    "noncomputable def expValue : ℂ := inner ℂ (A.1 ψ.1) ψ.1"
)
ENERGY_EXPECTATION_SPECIALIZATION = (
    "noncomputable def energyExpValue (ρ : DensityOperator H) "
    "(Hop : Observable H) : ℝ := ρ.observableExpectation Hop"
)
BORN_REAL_COMPATIBILITY = (
    "noncomputable def prob (P : POVM H M) (ρ : DensityOperator H) "
    "(m : M) : ℝ := probNNReal P ρ m"
)
BORN_PMF_SPECIALIZATION = (
    "noncomputable def bornPMF (P : POVM H M) (ρ : DensityOperator H) : PMF M := "
    "⟨fun m => (probNNReal P ρ m : ENNReal), "
    "(ENNReal.hasSum_coe).mpr (hasSum_probNNReal P ρ)⟩"
)
COUNTABLE_BRIDGE_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalExpectation"
)
COUNTABLE_FORMULA_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula"
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def normalized_code(path: Path) -> str:
    return " ".join(strip_lean_comments(path.read_text(encoding="utf-8")).split())


def documentation_files():
    for path in (ROOT / "README.md", ROOT / "PROJECT.md"):
        if path.exists():
            yield path
    for root in (NOTES, DOCS):
        if root.exists():
            yield from sorted(root.rglob("*.md"))


def check_documentation(errors: list[str]) -> None:
    check_absent_paths(
        errors,
        REMOVED_DOCUMENTS,
        root=ROOT,
        description="obsolete migration document exists",
    )

    for path in documentation_files():
        for line_no, line in numbered_lines(path):
            if TRACECLASS_NAMESPACE.search(line):
                errors.append(
                    f"obsolete public namespace in docs: {relative(path)}:{line_no}: {line.strip()}"
                )
            if LEGACY_QUANTUM_MODULE.search(line):
                errors.append(
                    f"obsolete QuantumTheory module in docs: {relative(path)}:{line_no}: {line.strip()}"
                )


def check_observable_expectation_boundary(errors: list[str]) -> None:
    postulates = normalized_code(EXPECTED_PURE_REAL_EXPECTATION)
    if CANONICAL_PURE_EXPECTATION_BODY not in postulates:
        errors.append(
            "pure-state expectation must use the canonical inner ψ (A ψ) orientation in "
            f"{relative(EXPECTED_PURE_REAL_EXPECTATION)}"
        )
    if LEGACY_REVERSED_PURE_EXPECTATION_BODY in postulates:
        errors.append(
            "legacy reversed pure-state expectation orientation in "
            f"{relative(EXPECTED_PURE_REAL_EXPECTATION)}"
        )

    pure_real_declarations: list[Path] = []
    density_real_declarations: list[Path] = []
    for path in lean_files(QUANTUM):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if PURE_REAL_EXPECTATION_DECL.search(code):
            pure_real_declarations.append(path)
        if DENSITY_REAL_EXPECTATION_DECL.search(code):
            density_real_declarations.append(path)
        if LEGACY_ENERGY_SELF_ADJOINT.search(code):
            errors.append(
                f"legacy Gibbs-owned generic observable expectation: {relative(path)}"
            )

    if pure_real_declarations != [EXPECTED_PURE_REAL_EXPECTATION]:
        rendered = ", ".join(relative(path) for path in pure_real_declarations) or "<none>"
        errors.append(
            "canonical pure-state real observable expectation must be declared exactly once in "
            f"{relative(EXPECTED_PURE_REAL_EXPECTATION)}; found: {rendered}"
        )

    if density_real_declarations != [EXPECTED_DENSITY_REAL_EXPECTATION]:
        rendered = ", ".join(relative(path) for path in density_real_declarations) or "<none>"
        errors.append(
            "canonical density-state real observable expectation must be declared exactly once in "
            f"{relative(EXPECTED_DENSITY_REAL_EXPECTATION)}; found: {rendered}"
        )

    energy_code = normalized_code(GIBBS_ENERGY_EXPECTATION)
    if ENERGY_EXPECTATION_SPECIALIZATION not in energy_code:
        errors.append(
            "energyExpValue must remain a direct specialization of "
            f"DensityOperator.observableExpectation in {relative(GIBBS_ENERGY_EXPECTATION)}"
        )


def check_born_probability_boundary(errors: list[str]) -> None:
    prob_nnreal_declarations: list[Path] = []
    born_pmf_declarations: list[Path] = []

    for path in lean_files(QUANTUM):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if PROB_NNREAL_DECL.search(code):
            prob_nnreal_declarations.append(path)
        if BORN_PMF_DECL.search(code):
            born_pmf_declarations.append(path)

    if prob_nnreal_declarations != [EXPECTED_BORN]:
        rendered = ", ".join(relative(path) for path in prob_nnreal_declarations) or "<none>"
        errors.append(
            "canonical nonnegative Born probability must be declared exactly once in "
            f"{relative(EXPECTED_BORN)}; found: {rendered}"
        )

    if born_pmf_declarations != [EXPECTED_BORN]:
        rendered = ", ".join(relative(path) for path in born_pmf_declarations) or "<none>"
        errors.append(
            "canonical Born probability mass function must be declared exactly once in "
            f"{relative(EXPECTED_BORN)}; found: {rendered}"
        )

    born_code = strip_lean_comments(EXPECTED_BORN.read_text(encoding="utf-8"))
    born_normalized = " ".join(born_code.split())

    if BORN_REAL_COMPATIBILITY not in born_normalized:
        errors.append(
            "prob must remain a direct real coercion of probNNReal in "
            f"{relative(EXPECTED_BORN)}"
        )

    if BORN_PMF_SPECIALIZATION not in born_normalized:
        errors.append(
            "bornPMF must remain the normalized ENNReal embedding of probNNReal in "
            f"{relative(EXPECTED_BORN)}"
        )

    kernel_match = PROBABILITY_KERNEL_DEF.search(born_code)
    if kernel_match is None:
        errors.append(
            f"missing canonical Born probability kernel in {relative(EXPECTED_BORN)}"
        )
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
    bridge_code = strip_lean_comments(
        COUNTABLE_DIAGONAL_BRIDGE.read_text(encoding="utf-8")
    )
    formula_code = strip_lean_comments(
        COUNTABLE_DIAGONAL_FORMULA.read_text(encoding="utf-8")
    )
    energy_code = strip_lean_comments(GIBBS_DIAGONAL_ENERGY.read_text(encoding="utf-8"))
    umbrella_code = DENSITY_UMBRELLA.read_text(encoding="utf-8")

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
                f"generic countable diagonal module has a finite-dimensional assumption: "
                f"{relative(path)}"
            )
        if "[Fintype" in code:
            errors.append(
                f"generic countable diagonal module has a finite-index assumption: "
                f"{relative(path)}"
            )

    if COUNTABLE_BRIDGE_IMPORT not in umbrella_code:
        errors.append(
            "density-state umbrella must import the Hilbert-Schmidt diagonal bridge: "
            f"{relative(DENSITY_UMBRELLA)}"
        )
    if COUNTABLE_FORMULA_IMPORT not in umbrella_code:
        errors.append(
            "density-state umbrella must import the countable diagonal formulas: "
            f"{relative(DENSITY_UMBRELLA)}"
        )

    if "theorem energyExpValue_eq_tsum_common_eigenbasis" not in energy_code:
        errors.append(
            "Gibbs diagonal energy must retain the HilbertBasis/tsum foundation in "
            f"{relative(GIBBS_DIAGONAL_ENERGY)}"
        )
    if "simpa using energyExpValue_eq_tsum_common_eigenbasis" not in normalized_code(
        GIBBS_DIAGONAL_ENERGY
    ):
        errors.append(
            "finite common-eigenbasis energy must delegate to the countable theorem in "
            f"{relative(GIBBS_DIAGONAL_ENERGY)}"
        )
    if "LinearMap.trace_eq_sum_inner" in energy_code:
        errors.append(
            "Gibbs diagonal energy must not rebuild the finite theorem through matrix trace in "
            f"{relative(GIBBS_DIAGONAL_ENERGY)}"
        )


def main() -> int:
    errors: list[str] = []
    density_declarations: list[Path] = []
    povm_declarations: list[Path] = []

    for path in lean_files(LEAN_ROOT):
        text = path.read_text(encoding="utf-8")

        if path.is_relative_to(QUANTUM) and path.name.endswith("TraceClass.lean"):
            errors.append(f"legacy QuantumTheory TraceClass file: {relative(path)}")

        for line_no, line in enumerate(text.splitlines(), start=1):
            if TRACECLASS_NAMESPACE.search(line):
                errors.append(
                    f"legacy QuantumTheory.TraceClass reference: {relative(path)}:{line_no}: {line.strip()}"
                )
            if TRACECLASS_QUANTUM_IMPORT.match(line):
                errors.append(
                    f"legacy QuantumTheory TraceClass import: {relative(path)}:{line_no}: {line.strip()}"
                )

        if path.is_relative_to(QUANTUM):
            if DENSITY_DECL.search(text):
                density_declarations.append(path)
            if POVM_DECL.search(text):
                povm_declarations.append(path)
            if LEGACY_ALIAS.search(text):
                errors.append(f"legacy compatibility alias: {relative(path)}")

    if density_declarations != [EXPECTED_DENSITY]:
        rendered = ", ".join(relative(path) for path in density_declarations) or "<none>"
        errors.append(
            "canonical DensityOperator must be declared exactly once in "
            f"{relative(EXPECTED_DENSITY)}; found: {rendered}"
        )

    if povm_declarations != [EXPECTED_POVM]:
        rendered = ", ".join(relative(path) for path in povm_declarations) or "<none>"
        errors.append(
            "canonical POVM must be declared exactly once in "
            f"{relative(EXPECTED_POVM)}; found: {rendered}"
        )

    check_observable_expectation_boundary(errors)
    check_born_probability_boundary(errors)
    check_countable_diagonal_boundary(errors)
    check_documentation(errors)

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
