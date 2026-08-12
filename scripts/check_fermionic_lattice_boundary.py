from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import finish_audit, lean_files, numbered_lines, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
LATTICE = FERMIONIC / "Lattice"
FIELD = FERMIONIC / "Field"

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

REMOVED_FIELD = tuple(
    FIELD / name
    for name in (
        "DiscreteLattice.lean",
        "Peierls.lean",
        "BoundedKuboBridge.lean",
        "BoundedMatrixUnitAdjoint.lean",
        "PeierlsContact.lean",
        "HermitianBondCurrent.lean",
        "RankOneSecondQuantization.lean",
        "GeometricCurrent.lean",
        "GeometricPeierls.lean",
    )
)

OLD_FIELD_MODULE = re.compile(
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Field\."
    r"(?:DiscreteLattice|Peierls|BoundedKuboBridge|BoundedMatrixUnitAdjoint|PeierlsContact|"
    r"HermitianBondCurrent|RankOneSecondQuantization|GeometricCurrent|GeometricPeierls)(?:\s|$)"
)

FORBIDDEN_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\."
    r"(?:SecondQuantization\.Fermionic\.(?:Field|Transport)|"
    r"QuantumTheory\.(?:LinearResponse|Transport))"
)

FORBIDDEN_RESPONSE_NAME = re.compile(
    r"\b(?:BoundedFreeSystem|NormalizedExpectation|retardedSusceptibility|"
    r"conductivity|Conductivity|Streda|Středa|FrequencyResponse)\b"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_layout(errors: list[str]) -> None:
    for path in REQUIRED:
        if not path.is_file():
            errors.append(f"missing fermionic lattice module: {rel(path)}")
    for path in REMOVED_FIELD:
        if path.exists():
            errors.append(f"obsolete Fermionic.Field lattice module still exists: {rel(path)}")


def check_lattice_boundary(errors: list[str]) -> None:
    for path in lean_files(LATTICE):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"lattice declaration remains in Field namespace: {rel(path)}")
        for line_no, line in enumerate(code.splitlines(), start=1):
            if FORBIDDEN_IMPORT.match(line):
                errors.append(f"lattice layer imports downstream theory: {rel(path)}:{line_no}: {line.strip()}")
            if FORBIDDEN_RESPONSE_NAME.search(line):
                errors.append(f"generic response/transport declaration leaked into lattice layer: {rel(path)}:{line_no}: {line.strip()}")


def check_old_paths(errors: list[str]) -> None:
    for path in lean_files(ROOT / "LeanCondensedMatter"):
        for line_no, line in numbered_lines(path):
            if OLD_FIELD_MODULE.search(line):
                errors.append(f"old Fermionic.Field lattice import remains: {rel(path)}:{line_no}: {line.strip()}")


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_lattice_boundary(errors)
    check_old_paths(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic lattice boundary audit failed:",
        success_message="Fermionic lattice boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
