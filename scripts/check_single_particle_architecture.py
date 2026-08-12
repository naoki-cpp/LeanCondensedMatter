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
LEAN_ROOT = ROOT / "LeanCondensedMatter"
QUANTUM_THEORY = LEAN_ROOT / "QuantumTheory"
SINGLE_PARTICLE = LEAN_ROOT / "QuantumMechanics" / "SingleParticle"
CONTINUUM = SINGLE_PARTICLE / "Continuum"
SECOND_QUANTIZATION = LEAN_ROOT / "SecondQuantization"
LEGACY_CONTINUUM_PATH = QUANTUM_THEORY / "Continuum"

SINGLE_PARTICLE_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.QuantumMechanics\.SingleParticle(?:\.|\s|$)"
)
SECOND_QUANTIZATION_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization(?:\.|\s|$)"
)
LEGACY_CONTINUUM_REFERENCE = re.compile(
    r"\b(?:LeanCondensedMatter\.)?QuantumTheory\.Continuum\b"
)
LEGACY_NESTED_CONTINUUM_NAMESPACE = re.compile(
    r"^\s*namespace\s+QuantumTheory\s*$\n\s*namespace\s+Continuum\s*$",
    re.MULTILINE,
)
CANONICAL_CONTINUUM_NAMESPACE = re.compile(
    r"(?:^\s*namespace\s+QuantumMechanics\.SingleParticle\.Continuum\s*$)"
    r"|(?:^\s*namespace\s+QuantumMechanics\s*$\n"
    r"\s*namespace\s+SingleParticle\s*$\n"
    r"\s*namespace\s+Continuum\s*$)",
    re.MULTILINE,
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_dependency_direction(errors: list[str]) -> None:
    for path in lean_files(QUANTUM_THEORY):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            if SINGLE_PARTICLE_IMPORT.match(line):
                errors.append(
                    "generic QuantumTheory imports concrete single-particle mechanics: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )

    for path in lean_files(SECOND_QUANTIZATION):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            if SINGLE_PARTICLE_IMPORT.match(line):
                errors.append(
                    "SecondQuantization imports concrete single-particle mechanics: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )

    for path in lean_files(SINGLE_PARTICLE):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            if SECOND_QUANTIZATION_IMPORT.match(line):
                errors.append(
                    "single-particle mechanics imports SecondQuantization: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )


def check_continuum_ownership(errors: list[str]) -> None:
    if LEGACY_CONTINUUM_PATH.exists():
        errors.append(
            "legacy concrete continuum owner exists: "
            f"{relative(LEGACY_CONTINUUM_PATH)}"
        )

    if not CONTINUUM.is_dir():
        errors.append(f"missing canonical single-particle continuum tree: {relative(CONTINUUM)}")
        return

    for path in lean_files(LEAN_ROOT):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))

        if LEGACY_NESTED_CONTINUUM_NAMESPACE.search(code):
            errors.append(
                "legacy nested QuantumTheory.Continuum namespace: "
                f"{relative(path)}"
            )

        for line_no, line in enumerate(code.splitlines(), start=1):
            if LEGACY_CONTINUUM_REFERENCE.search(line):
                errors.append(
                    "legacy QuantumTheory.Continuum path or namespace reference: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )

    for path in lean_files(CONTINUUM):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if not CANONICAL_CONTINUUM_NAMESPACE.search(code):
            errors.append(
                "single-particle continuum file does not declare the canonical namespace: "
                f"{relative(path)}"
            )


def main() -> int:
    errors: list[str] = []
    check_dependency_direction(errors)
    check_continuum_ownership(errors)
    return finish_audit(
        errors,
        failure_heading="Single-particle architecture audit failed:",
        success_message="Single-particle architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
