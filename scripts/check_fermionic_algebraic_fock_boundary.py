from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    numbered_lines,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
ALGEBRAIC = FERMIONIC / "Algebra" / "AlgebraicFock"
FIELD = FERMIONIC / "Field"

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

REMOVED_FIELD_FILES = tuple(
    FIELD / name
    for name in (
        "FiniteParticleFock.lean",
        "Creation.lean",
        "Annihilation.lean",
        "Mode.lean",
        "OccupationEquivalence.lean",
        "OccupationFieldEquivalence.lean",
        "SecondQuantization.lean",
        "SecondQuantizationLinearity.lean",
        "SecondQuantizationCommutator.lean",
    )
)

FORBIDDEN_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\."
    r"(?:SecondQuantization\.Fermionic\.(?:Field|Transport)|QuantumTheory\.Transport)"
)
FORBIDDEN_ANALYTIC_ASSUMPTION = re.compile(r"\b(?:Fintype|FiniteDimensional)\b")
OLD_FIELD_MODULE = re.compile(
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Field\."
    r"(?:FiniteParticleFock|Creation|Annihilation|Mode|OccupationEquivalence|"
    r"OccupationFieldEquivalence|SecondQuantization|SecondQuantizationLinearity|"
    r"SecondQuantizationCommutator)(?:\s|$)"
)

# These moved names have no competing Fermionic root API. Downstream files should therefore name
# the new owner explicitly rather than relying on the former Field namespace. Ambiguous names such
# as `create`, `annihilate`, and `vacuum` are intentionally excluded because the occupation-basis
# API owns declarations with those names as well.
UNAMBIGUOUS_MOVED_REFERENCES = (
    "dGamma",
    "dGammaLinear",
    "dGamma_linearCommutator",
    "linearCommutator",
    "occupationEquiv",
    "occupationConjugate",
    "occupationEquiv_create",
    "occupationEquiv_occupationConjugate_apply",
    "occupationAnnihilateFromField",
    "occupationAnnihilateFromField_eq_annihilate",
    "annihilateDual",
    "dualRankOne",
)
UNQUALIFIED_MOVED = {
    name: re.compile(rf"(?<![A-Za-z0-9_.]){re.escape(name)}(?![A-Za-z0-9_])")
    for name in UNAMBIGUOUS_MOVED_REFERENCES
}


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def check_layout(errors: list[str]) -> None:
    for path in REQUIRED_FILES:
        if not path.is_file():
            errors.append(f"missing algebraic Fock module: {relative(path)}")
    for path in REMOVED_FIELD_FILES:
        if path.exists():
            errors.append(f"removed Fermionic.Field algebra module still exists: {relative(path)}")


def check_algebra_boundary(errors: list[str]) -> None:
    for path in lean_files(ALGEBRAIC):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"algebraic Fock declaration remains in Field namespace: {relative(path)}")
        for line_no, line in enumerate(code.splitlines(), start=1):
            if FORBIDDEN_IMPORT.match(line):
                errors.append(
                    f"algebraic Fock imports downstream layer: {relative(path)}:{line_no}: {line.strip()}"
                )
            if FORBIDDEN_ANALYTIC_ASSUMPTION.search(line):
                errors.append(
                    f"finite-dimensional assumption in algebraic Fock core: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )


def check_old_imports(errors: list[str]) -> None:
    for path in lean_files(ROOT / "LeanCondensedMatter"):
        for line_no, line in numbered_lines(path):
            if OLD_FIELD_MODULE.search(line):
                errors.append(
                    f"old Fermionic.Field algebra import remains: "
                    f"{relative(path)}:{line_no}: {line.strip()}"
                )


def check_downstream_qualification(errors: list[str]) -> None:
    for path in lean_files(FIELD):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), start=1):
            for name, pattern in UNQUALIFIED_MOVED.items():
                if pattern.search(line):
                    errors.append(
                        f"unqualified moved algebraic Fock reference `{name}`: "
                        f"{relative(path)}:{line_no}: {line.strip()}"
                    )


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_algebra_boundary(errors)
    check_old_imports(errors)
    check_downstream_qualification(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic algebraic-Fock boundary audit failed:",
        success_message="Fermionic algebraic-Fock boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
