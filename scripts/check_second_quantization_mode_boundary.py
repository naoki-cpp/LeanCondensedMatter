from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
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
LEGACY_MODE_COUNT = re.compile(r"\bmodeCount\b")


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


def check_mode_boundary(errors: list[str]) -> None:
    for path in DIMENSION_INDEPENDENT_MODE_FILES:
        if not path.is_file():
            errors.append(f"missing dimension-independent mode module: {relative(path)}")
            continue

        code = strip_comments(path.read_text(encoding="utf-8"))
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

    for path in lean_files(SQ):
        code = strip_comments(path.read_text(encoding="utf-8"))
        for match in LEGACY_MODE_COUNT.finditer(code):
            line_no = code.count("\n", 0, match.start()) + 1
            errors.append(
                f"legacy global mode count: {relative(path)}:{line_no}: {match.group(0)}"
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
