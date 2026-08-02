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


def main() -> int:
    errors: list[str] = []

    if REMOVED_FILE.exists():
        errors.append(f"removed unused module exists: {relative(REMOVED_FILE)}")

    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
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
