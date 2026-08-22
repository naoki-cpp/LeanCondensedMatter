from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"

MODE_LABEL_FILE = SQ / "Common" / "Algebra" / "OneParticleSpace.lean"
DIMENSION_INDEPENDENT_MODE_FILES = (
    MODE_LABEL_FILE,
    SQ / "Common" / "Algebra" / "OccupationBasis.lean",
    SQ / "Common" / "Algebra" / "AlgebraicFock.lean",
    SQ / "Fermionic" / "Algebra" / "Occupation.lean",
    SQ / "Fermionic" / "Algebra" / "FockSpace.lean",
    SQ / "Bosonic" / "Algebra" / "Occupation.lean",
    SQ / "Bosonic" / "Algebra" / "FockSpace.lean",
)

FINITE_MODE_ASSUMPTION = re.compile(r"\[\s*(?:Fintype|Finite)\s+Mode\s*\]")
MODE_LABEL_TYPECLASS = re.compile(r"\b(?:Fintype|Finite|DecidableEq)\b")


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_mode_boundary(errors: list[str]) -> None:
    for path in DIMENSION_INDEPENDENT_MODE_FILES:
        if not path.is_file():
            errors.append(f"missing dimension-independent mode module: {relative(path)}")
            continue

        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            if FINITE_MODE_ASSUMPTION.search(line):
                errors.append(
                    "finite-mode assumption in foundational algebra: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )

            if path == MODE_LABEL_FILE and MODE_LABEL_TYPECLASS.search(line):
                errors.append(
                    "typeclass assumption in foundational mode-label module: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )


def main() -> int:
    errors: list[str] = []
    check_mode_boundary(errors)
    return finish_audit(
        errors,
        failure_heading="SecondQuantization mode-boundary audit failed:",
        success_message="SecondQuantization mode-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
