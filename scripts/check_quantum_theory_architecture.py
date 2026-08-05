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
LEGACY_ENERGY_SELF_ADJOINT = re.compile(r"\benergyExpectationSelfAdjoint\b")

EXPECTED_DENSITY = QUANTUM / "DensityOperator" / "Basic.lean"
EXPECTED_POVM = QUANTUM / "POVM" / "Basic.lean"
EXPECTED_PURE_REAL_EXPECTATION = QUANTUM / "Postulates.lean"
EXPECTED_DENSITY_REAL_EXPECTATION = (
    QUANTUM / "DensityOperator" / "ObservableExpectation.lean"
)
GIBBS_ENERGY_EXPECTATION = QUANTUM / "Gibbs" / "EnergyExpectation.lean"
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


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving newlines."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def normalized_code(path: Path) -> str:
    return " ".join(strip_comments(path.read_text(encoding="utf-8")).split())


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
        code = strip_comments(path.read_text(encoding="utf-8"))
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
    check_documentation(errors)

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
