from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    ImportBoundary,
    check_import_boundaries,
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

QUANTUM_MECHANICS_PREFIX = "LeanCondensedMatter.QuantumMechanics"
SECOND_QUANTIZATION_PREFIX = "LeanCondensedMatter.SecondQuantization"

DEPENDENCY_BOUNDARIES = (
    ImportBoundary(
        QUANTUM_THEORY,
        (QUANTUM_MECHANICS_PREFIX,),
        "generic QuantumTheory must remain upstream of QuantumMechanics",
    ),
    ImportBoundary(
        SECOND_QUANTIZATION,
        (QUANTUM_MECHANICS_PREFIX,),
        "SecondQuantization must remain independent of concrete QuantumMechanics",
    ),
    ImportBoundary(
        SINGLE_PARTICLE,
        (SECOND_QUANTIZATION_PREFIX,),
        "single-particle mechanics must remain upstream of SecondQuantization",
    ),
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
    check_import_boundaries(errors, DEPENDENCY_BOUNDARIES, root=ROOT)


def check_continuum_ownership(errors: list[str]) -> None:
    if not CONTINUUM.is_dir():
        errors.append(f"missing canonical single-particle continuum tree: {relative(CONTINUUM)}")
        return

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
