from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    module_matches_prefix,
    numbered_imports,
    relative,
    repository_root,
)

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC_DIAGRAMMATICS = SQ / "Fermionic" / "Diagrammatics"
TWO_POINT_EXPANSION = FERMIONIC_DIAGRAMMATICS / "TwoPointDiagramExpansion"
COMMON_TWO_POINT = SQ / "Common" / "Diagrammatics" / "TwoPoint"
COMMON_QUARTIC = SQ / "Common" / "Diagrammatics" / "Quartic"
BOSONIC_QUARTIC = SQ / "Bosonic" / "Diagrammatics" / "Quartic"

TWO_POINT_LAYERS = ("Semantics", "Factorization", "Analysis", "Integration", "Series")
TWO_POINT_LAYER_RANK = {name: rank for rank, name in enumerate(TWO_POINT_LAYERS)}
TWO_POINT_PREFIX = (
    "LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion"
)
LINKED_CLUSTER_PREFIX = (
    "LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster"
)
BOSONIC_QUARTIC_PREFIX = (
    "LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic"
)
BOSONIC_THERMAL_PREFIX = f"{BOSONIC_QUARTIC_PREFIX}.Thermal"


def describe(path: Path) -> str:
    return relative(ROOT, path)


def check_layout(errors: list[str]) -> None:
    # These owners are layered directory APIs; leaf modules belong below their layer directory.
    for root in (COMMON_TWO_POINT, COMMON_QUARTIC, TWO_POINT_EXPANSION):
        if not root.is_dir():
            errors.append(f"missing diagrammatics owner directory: {describe(root)}")
            continue
        for path in sorted(root.glob("*.lean")):
            errors.append(f"flat module bypasses diagrammatics layer ownership: {describe(path)}")


def imported_two_point_layer(imported: str) -> str | None:
    prefix = TWO_POINT_PREFIX + "."
    if not imported.startswith(prefix):
        return None
    layer = imported[len(prefix):].split(".", maxsplit=1)[0]
    return layer if layer in TWO_POINT_LAYER_RANK else None


def check_two_point_layer_direction(errors: list[str]) -> None:
    for source_layer in TWO_POINT_LAYERS:
        source_root = TWO_POINT_EXPANSION / source_layer
        if not source_root.is_dir():
            errors.append(f"missing two-point expansion layer: {describe(source_root)}")
            continue

        source_rank = TWO_POINT_LAYER_RANK[source_layer]
        for path in lean_files(source_root):
            for line_no, imported in numbered_imports(path):
                if imported == TWO_POINT_PREFIX:
                    errors.append(
                        "two-point expansion layer imports umbrella: "
                        f"{describe(path)}:{line_no}: `{imported}`"
                    )
                    continue

                target_layer = imported_two_point_layer(imported)
                if target_layer is not None and TWO_POINT_LAYER_RANK[target_layer] > source_rank:
                    errors.append(
                        "two-point expansion imports higher layer: "
                        f"{describe(path)}:{line_no}: {source_layer} -> {target_layer}: `{imported}`"
                    )

                if module_matches_prefix(imported, LINKED_CLUSTER_PREFIX):
                    errors.append(
                        "two-point expansion imports linked-cluster endpoint: "
                        f"{describe(path)}:{line_no}: `{imported}`"
                    )


def check_bosonic_thermal_direction(errors: list[str]) -> None:
    if not BOSONIC_QUARTIC.is_dir():
        errors.append(f"missing bosonic quartic owner: {describe(BOSONIC_QUARTIC)}")
        return

    for path in lean_files(BOSONIC_QUARTIC):
        rel = path.relative_to(BOSONIC_QUARTIC)
        if rel.parts and rel.parts[0] == "Thermal":
            continue
        for line_no, imported in numbered_imports(path):
            if module_matches_prefix(imported, BOSONIC_THERMAL_PREFIX):
                errors.append(
                    "bosonic quartic semantics imports thermal layer: "
                    f"{describe(path)}:{line_no}: `{imported}`"
                )
            if imported == BOSONIC_QUARTIC_PREFIX:
                errors.append(
                    "bosonic quartic semantics imports umbrella: "
                    f"{describe(path)}:{line_no}: `{imported}`"
                )


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_two_point_layer_direction(errors)
    check_bosonic_thermal_direction(errors)
    return finish_audit(
        errors,
        failure_heading="Diagrammatics layer architecture audit failed:",
        success_message="Diagrammatics layer architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
