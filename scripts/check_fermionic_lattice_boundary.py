from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    ImportBoundary,
    check_import_boundaries,
    finish_audit,
    lean_files,
    repository_root,
    require_files,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
LATTICE = FERMIONIC / "Lattice"

REQUIRED = (
    FERMIONIC / "Lattice.lean",
    LATTICE / "DiscreteLattice.lean",
    LATTICE / "Peierls.lean",
    LATTICE / "Bounded.lean",
    LATTICE / "BoundedMatrixUnitAdjoint.lean",
    LATTICE / "PeierlsContact.lean",
    LATTICE / "HermitianBondCurrent.lean",
    LATTICE / "RankOneSecondQuantization.lean",
    LATTICE / "GeometricCurrent.lean",
    LATTICE / "GeometricPeierls.lean",
)

# The global Fermionic layer DAG is owned by check_fermionic_transport_validation_boundary.py.
# This focused audit adds the domain rule that lattice construction is upstream of response theory.
DOMAIN_BOUNDARIES = (
    ImportBoundary(
        LATTICE,
        (
            "LeanCondensedMatter.QuantumTheory.LinearResponse",
            "LeanCondensedMatter.QuantumTheory.Transport",
        ),
        "fermionic lattice construction must remain upstream of response/transport theory",
    ),
)

FORBIDDEN_RESPONSE_NAME = re.compile(
    r"\b(?:BoundedFreeSystem|NormalizedExpectation|retardedSusceptibility|"
    r"conductivity|Conductivity|Streda|Středa|FrequencyResponse)\b"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_layout(errors: list[str]) -> None:
    require_files(errors, REQUIRED, root=ROOT, description="fermionic lattice owner")


def check_lattice_boundary(errors: list[str]) -> None:
    check_import_boundaries(errors, DOMAIN_BOUNDARIES, root=ROOT)

    for path in lean_files(LATTICE):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"lattice declaration is outside its path-owned namespace: {rel(path)}")
        for line_no, line in enumerate(code.splitlines(), start=1):
            if FORBIDDEN_RESPONSE_NAME.search(line):
                errors.append(
                    "generic response/transport declaration leaked into lattice layer: "
                    f"{rel(path)}:{line_no}: {line.strip()}"
                )


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_lattice_boundary(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic lattice boundary audit failed:",
        success_message="Fermionic lattice boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
