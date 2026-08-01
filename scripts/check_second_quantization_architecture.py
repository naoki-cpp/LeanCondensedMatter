from __future__ import annotations

import re
import sys
from pathlib import Path

from audit_second_quantization_namespaces import collect_findings

ROOT = Path(__file__).resolve().parents[1]
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"

REMOVED_FILES = (
    SQ / "Common.lean",
    SQ / "Fermionic.lean",
    SQ / "Bosonic.lean",
    SQ / "Fermionic" / "Perturbation" / "DysonExpansion.lean",
    SQ / "Fermionic" / "Perturbation" / "ContinuousDyson.lean",
)

REMOVED_DIRECTORIES = (
    SQ / "Bosonic" / "Foundations",
    SQ / "Bosonic" / "OperatorAlgebra",
)

REMOVED_EXACT_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.(Common|Fermionic|Bosonic)\s*$"
)
REMOVED_BOSONIC_PATH = re.compile(
    r"LeanCondensedMatter\.SecondQuantization\.Bosonic\.(Foundations|OperatorAlgebra)(?:\.|\s|$)"
)
STATISTICS_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.(Fermionic|Bosonic)(?:\.|\s|$)"
)
PHYSICS_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization(?:\.|\s|$)"
)
LEGACY_FERMIONIC_IDENTIFIER = re.compile(
    r"FockSpaceFermionic|FermionOccupation|fermionParticleNumber|fermionVacuum"
)
FERMIONIC_DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:private|protected)\s+)?(?:noncomputable\s+)?"
    r"(?:abbrev|def|theorem|lemma|instance|structure|class|inductive|opaque)\b"
)
CANONICAL_FERMIONIC_NAMESPACE = "namespace SecondQuantization\nnamespace Fermionic"


def lean_files(root: Path):
    yield from sorted(root.rglob("*.lean"))


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_removed_paths(errors: list[str]) -> None:
    for path in REMOVED_FILES:
        if path.exists():
            errors.append(f"removed compatibility module exists: {relative(path)}")
    for path in REMOVED_DIRECTORIES:
        if path.exists():
            errors.append(f"removed directory exists: {relative(path)}")

    for path in lean_files(ROOT / "LeanCondensedMatter"):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if REMOVED_EXACT_IMPORT.match(line):
                errors.append(f"removed umbrella import: {relative(path)}:{line_no}: {line.strip()}")
            if REMOVED_BOSONIC_PATH.search(line):
                errors.append(f"removed bosonic path: {relative(path)}:{line_no}: {line.strip()}")
            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion":
                errors.append(
                    f"removed fermionic Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )
            if line.strip() == "import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson":
                errors.append(
                    f"removed fermionic continuous-Dyson import: {relative(path)}:{line_no}: {line.strip()}"
                )


def check_dependency_direction(errors: list[str]) -> None:
    for path in lean_files(SQ / "Common"):
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if STATISTICS_IMPORT.match(line):
                errors.append(
                    f"Common imports statistics-specific code: {relative(path)}:{line_no}: {line.strip()}"
                )

    for area in ("Analysis", "Combinatorics"):
        root = ROOT / "LeanCondensedMatter" / area
        for path in lean_files(root):
            for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                if PHYSICS_IMPORT.match(line):
                    errors.append(
                        f"{area} imports SecondQuantization: {relative(path)}:{line_no}: {line.strip()}"
                    )


def check_fermionic_namespace(errors: list[str]) -> None:
    for path in lean_files(ROOT / "LeanCondensedMatter"):
        text = path.read_text(encoding="utf-8")
        for match in LEGACY_FERMIONIC_IDENTIFIER.finditer(text):
            line_no = text.count("\n", 0, match.start()) + 1
            errors.append(
                f"legacy fermionic identifier: {relative(path)}:{line_no}: {match.group(0)}"
            )

    for path in lean_files(SQ / "Fermionic"):
        text = path.read_text(encoding="utf-8")
        if not FERMIONIC_DECLARATION.search(text):
            continue
        root_blocks = len(re.findall(r"(?m)^namespace SecondQuantization\s*$", text))
        canonical_blocks = text.count(CANONICAL_FERMIONIC_NAMESPACE)
        if root_blocks == 0 or root_blocks != canonical_blocks:
            errors.append(
                f"fermionic declarations outside canonical namespace: {relative(path)}"
            )


def check_declaration_namespaces(errors: list[str]) -> None:
    misplaced, statistic_names, _ = collect_findings()
    for finding in misplaced:
        errors.append(
            "declaration outside path-owned namespace: "
            f"{relative(finding.path)}:{finding.line}: "
            f"{finding.kind} {finding.name} in {finding.namespace}"
        )
    for finding in statistic_names:
        errors.append(
            "statistic-encoded declaration name: "
            f"{relative(finding.path)}:{finding.line}: {finding.name}"
        )


def check_entry_point(errors: list[str]) -> None:
    entry = SQ.with_suffix(".lean")
    if not entry.is_file():
        errors.append(f"missing canonical entry point: {relative(entry)}")

    root_module = ROOT / "LeanCondensedMatter.lean"
    expected = "import LeanCondensedMatter.SecondQuantization"
    if expected not in root_module.read_text(encoding="utf-8").splitlines():
        errors.append(f"repository root does not import canonical entry point: {expected}")


def main() -> int:
    errors: list[str] = []
    check_removed_paths(errors)
    check_dependency_direction(errors)
    check_fermionic_namespace(errors)
    check_declaration_namespaces(errors)
    check_entry_point(errors)

    if errors:
        print("SecondQuantization architecture check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("SecondQuantization architecture check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
