from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "LeanCondensedMatter"

REMOVED_IDENTIFIERS = {
    "QuarticWickDiagram.ext": "removed Fermionic WickDiagram ext wrapper",
    "QuarticWickDiagram.equivPair": "removed Fermionic WickDiagram equivPair wrapper",
}


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def main() -> int:
    errors: list[str] = []

    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for identifier, description in REMOVED_IDENTIFIERS.items():
                if identifier in line:
                    errors.append(
                        f"{description}: {relative(path)}:{line_no}: {line.strip()}"
                    )

    if errors:
        print("Removed SecondQuantization identifier check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Removed SecondQuantization identifier check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
