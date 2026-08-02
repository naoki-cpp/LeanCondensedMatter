from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = (
    ROOT
    / "LeanCondensedMatter"
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "BlochDeDominicis"
    / "ExpectationRecursion.lean"
)

ALLOWED_IMPORTS = {
    "import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight",
    "import LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion",
}

FORBIDDEN_IDENTIFIERS = {
    re.compile(r"(?<![A-Za-z0-9_'])Fintype(?![A-Za-z0-9_'])"):
        "finite configuration assumption",
    re.compile(r"(?<![A-Za-z0-9_'])AlgebraicFock(?![A-Za-z0-9_'])"):
        "algebraic-Fock implementation type",
    re.compile(r"(?<![A-Za-z0-9_'])finiteGibbsExpectation(?![A-Za-z0-9_'])"):
        "finite Gibbs expectation implementation",
    re.compile(r"(?<![A-Za-z0-9_'])DensityOperator(?![A-Za-z0-9_'])"):
        "density-operator implementation",
    re.compile(r"(?<![A-Za-z0-9_'])FiniteHilbert[A-Za-z0-9_']*(?![A-Za-z0-9_'])"):
        "finite Hilbert realization",
    re.compile(r"(?<![A-Za-z0-9_'])traceFock(?![A-Za-z0-9_'])"):
        "finite trace implementation",
    re.compile(r"(?<![A-Za-z0-9_'])diagonalEvolution(?![A-Za-z0-9_'])"):
        "finite diagonal-evolution implementation",
    re.compile(r"(?<![A-Za-z0-9_'])normalizedWeightedDiagonal(?![A-Za-z0-9_'])"):
        "normalized occupation-basis implementation",
    re.compile(r"(?<![A-Za-z0-9_'])weightedTrace(?![A-Za-z0-9_'])"):
        "weighted occupation-basis implementation",
}


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

    if not TARGET.is_file():
        errors.append(f"missing generic expectation recursion module: {relative(TARGET)}")
    else:
        raw = TARGET.read_text(encoding="utf-8")
        for line_no, line in enumerate(raw.splitlines(), start=1):
            stripped = line.strip()
            if stripped.startswith("import ") and stripped not in ALLOWED_IMPORTS:
                errors.append(
                    "generic expectation recursion has a non-generic import: "
                    f"{relative(TARGET)}:{line_no}: {stripped}"
                )

        code = strip_comments(raw)
        for line_no, line in enumerate(code.splitlines(), start=1):
            for pattern, description in FORBIDDEN_IDENTIFIERS.items():
                if match := pattern.search(line):
                    errors.append(
                        f"generic expectation recursion mentions {description}: "
                        f"{relative(TARGET)}:{line_no}: {match.group(0)}"
                    )

    if errors:
        print("Bloch-de Dominicis expectation boundary check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("Bloch-de Dominicis expectation boundary check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
