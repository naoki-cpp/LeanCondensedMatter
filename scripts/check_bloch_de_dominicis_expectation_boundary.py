from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    require_files,
    require_import,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
TARGET = (
    ROOT
    / "LeanCondensedMatter"
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "BlochDeDominicis"
    / "ExpectationRecursion.lean"
)

REQUIRED_IMPORTS = (
    "LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight",
    "LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion",
)

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


def main() -> int:
    errors: list[str] = []

    require_files(errors, (TARGET,), root=ROOT, description="generic expectation recursion module")
    if errors:
        return finish_audit(
            errors,
            failure_heading="Bloch-de Dominicis expectation boundary check failed:",
            success_message="Bloch-de Dominicis expectation boundary check passed",
        )

    for imported in REQUIRED_IMPORTS:
        require_import(
            errors,
            TARGET,
            imported,
            root=ROOT,
            description="generic expectation recursion module",
        )

    code = strip_lean_comments(TARGET.read_text(encoding="utf-8"))
    for line_no, line in enumerate(code.splitlines(), start=1):
        for pattern, description in FORBIDDEN_IDENTIFIERS.items():
            if match := pattern.search(line):
                errors.append(
                    f"generic expectation recursion mentions {description}: "
                    f"{relative(TARGET)}:{line_no}: {match.group(0)}"
                )

    return finish_audit(
        errors,
        failure_heading="Bloch-de Dominicis expectation boundary check failed:",
        success_message="Bloch-de Dominicis expectation boundary check passed",
    )


if __name__ == "__main__":
    raise SystemExit(main())
