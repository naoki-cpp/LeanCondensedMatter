from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import finish_audit, lean_files, numbered_lines, relative, repository_root

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC_DIAGRAMMATICS = SQ / "Fermionic" / "Diagrammatics"
TWO_POINT_EXPANSION = FERMIONIC_DIAGRAMMATICS / "TwoPointDiagramExpansion"
COMMON_TWO_POINT = SQ / "Common" / "Diagrammatics" / "TwoPoint"
COMMON_QUARTIC = SQ / "Common" / "Diagrammatics" / "Quartic"
BOSONIC_QUARTIC = SQ / "Bosonic" / "Diagrammatics" / "Quartic"

TWO_POINT_LAYERS = ("Semantics", "Factorization", "Analysis", "Integration", "Series")
TWO_POINT_LAYER_RANK = {name: rank for rank, name in enumerate(TWO_POINT_LAYERS)}
TWO_POINT_LAYER_IMPORT = re.compile(
    r"^\s*import\s+"
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Diagrammatics\."
    r"TwoPointDiagramExpansion\.(Semantics|Factorization|Analysis|Integration|Series)"
    r"(?:\.|\s|$)"
)
TWO_POINT_UMBRELLA_IMPORT = re.compile(
    r"^\s*import\s+"
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Diagrammatics\."
    r"TwoPointDiagramExpansion\s*$"
)
LINKED_CLUSTER_IMPORT = re.compile(
    r"^\s*import\s+"
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Diagrammatics\.LinkedCluster"
    r"(?:\.|\s|$)"
)
BOSONIC_THERMAL_IMPORT = re.compile(
    r"^\s*import\s+"
    r"LeanCondensedMatter\.SecondQuantization\.Bosonic\.Diagrammatics\.Quartic\.Thermal"
    r"(?:\.|\s|$)"
)
BOSONIC_QUARTIC_UMBRELLA_IMPORT = re.compile(
    r"^\s*import\s+"
    r"LeanCondensedMatter\.SecondQuantization\.Bosonic\.Diagrammatics\.Quartic\s*$"
)

REMOVED_FERMIONIC_LINKED_CLUSTER_PATHS = (
    FERMIONIC_DIAGRAMMATICS / "DysonConnectedDiagramExpansion.lean",
    FERMIONIC_DIAGRAMMATICS / "DysonLinkedClusterTheorem.lean",
    FERMIONIC_DIAGRAMMATICS / "DysonLinkedClusterLowOrder.lean",
)


def describe(path: Path) -> str:
    return relative(ROOT, path)


def check_no_flat_modules(errors: list[str]) -> None:
    for root in (COMMON_TWO_POINT, COMMON_QUARTIC, TWO_POINT_EXPANSION):
        if not root.is_dir():
            errors.append(f"missing diagrammatics owner directory: {describe(root)}")
            continue
        for path in sorted(root.glob("*.lean")):
            errors.append(f"obsolete flat diagrammatics module exists: {describe(path)}")

    for path in REMOVED_FERMIONIC_LINKED_CLUSTER_PATHS:
        if path.exists():
            errors.append(f"obsolete linked-cluster root module exists: {describe(path)}")


def check_two_point_layer_direction(errors: list[str]) -> None:
    for source_layer in TWO_POINT_LAYERS:
        source_root = TWO_POINT_EXPANSION / source_layer
        if not source_root.is_dir():
            errors.append(f"missing two-point expansion layer: {describe(source_root)}")
            continue

        source_rank = TWO_POINT_LAYER_RANK[source_layer]
        for path in lean_files(source_root):
            for line_no, line in numbered_lines(path):
                stripped = line.strip()
                if match := TWO_POINT_LAYER_IMPORT.match(line):
                    target_layer = match.group(1)
                    if TWO_POINT_LAYER_RANK[target_layer] > source_rank:
                        errors.append(
                            "two-point expansion imports higher layer: "
                            f"{describe(path)}:{line_no}: {source_layer} -> {target_layer}: {stripped}"
                        )
                if TWO_POINT_UMBRELLA_IMPORT.match(line):
                    errors.append(
                        "two-point expansion layer imports umbrella: "
                        f"{describe(path)}:{line_no}: {stripped}"
                    )
                if LINKED_CLUSTER_IMPORT.match(line):
                    errors.append(
                        "two-point expansion imports linked-cluster endpoint: "
                        f"{describe(path)}:{line_no}: {stripped}"
                    )


def check_bosonic_thermal_direction(errors: list[str]) -> None:
    if not BOSONIC_QUARTIC.is_dir():
        errors.append(f"missing bosonic quartic owner: {describe(BOSONIC_QUARTIC)}")
        return

    for path in lean_files(BOSONIC_QUARTIC):
        rel = path.relative_to(BOSONIC_QUARTIC)
        if rel.parts and rel.parts[0] == "Thermal":
            continue
        for line_no, line in numbered_lines(path):
            stripped = line.strip()
            if BOSONIC_THERMAL_IMPORT.match(line):
                errors.append(
                    "bosonic quartic semantics imports thermal layer: "
                    f"{describe(path)}:{line_no}: {stripped}"
                )
            if BOSONIC_QUARTIC_UMBRELLA_IMPORT.match(line):
                errors.append(
                    "bosonic quartic semantics imports umbrella: "
                    f"{describe(path)}:{line_no}: {stripped}"
                )


def main() -> int:
    errors: list[str] = []
    check_no_flat_modules(errors)
    check_two_point_layer_direction(errors)
    check_bosonic_thermal_direction(errors)
    return finish_audit(
        errors,
        failure_heading="Diagrammatics layer architecture check failed:",
        success_message="Diagrammatics layer architecture check passed",
    )


if __name__ == "__main__":
    raise SystemExit(main())
