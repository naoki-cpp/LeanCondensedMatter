from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
    require_files,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
ALGEBRAIC = FERMIONIC / "Algebra" / "AlgebraicFock"

REQUIRED_FILES = (
    FERMIONIC / "Algebra" / "AlgebraicFock.lean",
    ALGEBRAIC / "Basic.lean",
    ALGEBRAIC / "Creation.lean",
    ALGEBRAIC / "Annihilation.lean",
    ALGEBRAIC / "Mode.lean",
    ALGEBRAIC / "OccupationEquivalence.lean",
    ALGEBRAIC / "OccupationFieldEquivalence.lean",
    ALGEBRAIC / "SecondQuantization.lean",
    ALGEBRAIC / "SecondQuantizationLinearity.lean",
    ALGEBRAIC / "SecondQuantizationCommutator.lean",
    ALGEBRAIC / "RankOne.lean",
)

FORBIDDEN_ANALYTIC_ASSUMPTION = re.compile(r"\b(?:Fintype|FiniteDimensional)\b")


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_layout(errors: list[str]) -> None:
    require_files(errors, REQUIRED_FILES, root=ROOT, description="fermionic algebraic-Fock owner")


def check_algebra_boundary(errors: list[str]) -> None:
    # AlgebraicFock -> QuantumTheory.Transport direction is owned by the shared scoped DAG.
    for path in lean_files(ALGEBRAIC):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(
                f"algebraic Fock declaration is outside its path-owned namespace: {relative(path)}"
            )
        for line_no, line in enumerate(code.splitlines(), start=1):
            if FORBIDDEN_ANALYTIC_ASSUMPTION.search(line):
                errors.append(
                    "finite-dimensional assumption in algebraic Fock core: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_algebra_boundary(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic algebraic-Fock boundary audit failed:",
        success_message="Fermionic algebraic-Fock boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
