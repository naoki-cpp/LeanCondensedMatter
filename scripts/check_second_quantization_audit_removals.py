from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "LeanCondensedMatter"
REMOVED_FILE = (
    LEAN_ROOT
    / "SecondQuantization"
    / "Bosonic"
    / "Diagrammatics"
    / "QuarticLegFamily.lean"
)
REMOVED_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics."
    "QuarticLegFamily"
)


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments while preserving line numbers."""
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


def main() -> int:
    errors: list[str] = []

    if REMOVED_FILE.exists():
        errors.append(f"removed unused module exists: {relative(REMOVED_FILE)}")

    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            if line.strip() == REMOVED_IMPORT:
                errors.append(
                    f"removed unused import: {relative(path)}:{line_no}: {line.strip()}"
                )

    if errors:
        print("SecondQuantization final-audit removal check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("SecondQuantization final-audit removal check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
