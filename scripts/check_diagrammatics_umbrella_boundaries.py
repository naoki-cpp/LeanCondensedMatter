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
TWO_POINT_EXPANSION = (
    SQ / "Fermionic" / "Diagrammatics" / "TwoPointDiagramExpansion"
)
BOSONIC_QUARTIC = SQ / "Bosonic" / "Diagrammatics" / "Quartic"

TWO_POINT_UMBRELLA = (
    "LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion"
)
LINKED_CLUSTER_PREFIX = (
    "LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster"
)
BOSONIC_QUARTIC_UMBRELLA = (
    "LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic"
)


def describe(path: Path) -> str:
    return relative(ROOT, path)


def check_two_point_endpoint_boundary(errors: list[str]) -> None:
    # Stage ordering is owned by the scoped DAG. This focused rule only prevents implementation
    # modules from importing public endpoints whose module prefixes cannot be separated cleanly in
    # that DAG without classifying future owner paths as historical layers.
    for path in lean_files(TWO_POINT_EXPANSION):
        for line_no, imported in numbered_imports(path):
            if imported == TWO_POINT_UMBRELLA or module_matches_prefix(
                imported, LINKED_CLUSTER_PREFIX
            ):
                errors.append(
                    "two-point expansion implementation imports public endpoint: "
                    f"{describe(path)}:{line_no}: `{imported}`"
                )


def check_bosonic_umbrella_boundary(errors: list[str]) -> None:
    # Thermal direction is graph-owned. The exact umbrella import is a source-topology rule because
    # the umbrella intentionally shares the same module prefix as its semantic descendants.
    for path in lean_files(BOSONIC_QUARTIC):
        rel = path.relative_to(BOSONIC_QUARTIC)
        if rel.parts and rel.parts[0] == "Thermal":
            continue
        for line_no, imported in numbered_imports(path):
            if imported == BOSONIC_QUARTIC_UMBRELLA:
                errors.append(
                    "bosonic quartic semantics imports umbrella: "
                    f"{describe(path)}:{line_no}: `{imported}`"
                )


def main() -> int:
    errors: list[str] = []
    check_two_point_endpoint_boundary(errors)
    check_bosonic_umbrella_boundary(errors)
    return finish_audit(
        errors,
        failure_heading="Diagrammatics umbrella-boundary audit failed:",
        success_message="Diagrammatics umbrella-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
