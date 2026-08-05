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

EXPECTED_DENSITY = QUANTUM / "DensityOperator" / "Basic.lean"
EXPECTED_POVM = QUANTUM / "POVM" / "Basic.lean"
REMOVED_DOCUMENTS = (
    NOTES / "migrations" / "canonical-quantum-density-theory.md",
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


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

    check_documentation(errors)

    return finish_audit(
        errors,
        failure_heading="QuantumTheory architecture audit failed:",
        success_message="QuantumTheory architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
