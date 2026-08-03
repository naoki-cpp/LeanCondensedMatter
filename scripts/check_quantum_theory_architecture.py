from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
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
    return str(path.relative_to(ROOT))


def lean_files(root: Path):
    yield from sorted(root.rglob("*.lean"))


def documentation_files():
    for path in (ROOT / "README.md", ROOT / "PROJECT.md"):
        if path.exists():
            yield path
    for root in (NOTES, DOCS):
        if root.exists():
            yield from sorted(root.rglob("*.md"))


def check_documentation(errors: list[str]) -> None:
    for path in REMOVED_DOCUMENTS:
        if path.exists():
            errors.append(f"obsolete migration document exists: {relative(path)}")

    for path in documentation_files():
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
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

    if errors:
        print("QuantumTheory architecture audit failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("QuantumTheory architecture audit passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
