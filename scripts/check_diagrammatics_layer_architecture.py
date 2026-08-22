from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
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
BOSONIC_QUARTIC_PREFIX = (
    "LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic"
)


def describe(path: Path) -> str:
    return relative(ROOT, path)


def check_layout(errors: list[str]) -> None:
    # Import ordering is owned by the shared scoped DAG. Keep only physical source-layout rules here.
    for root in (COMMON_TWO_POINT, COMMON_QUARTIC, TWO_POINT_EXPANSION):
        if not root.is_dir():
            errors.append(f"missing diagrammatics owner directory: {describe(root)}")
            continue
        for path in sorted(root.glob("*.lean")):
            errors.append(f"flat module bypasses diagrammatics layer ownership: {describe(path)}")

    for layer in TWO_POINT_LAYERS:
        source_root = TWO_POINT_EXPANSION / layer
        if not source_root.is_dir():
            errors.append(f"missing two-point expansion layer: {describe(source_root)}")


def check_bosonic_umbrella_boundary(errors: list[str]) -> None:
    if not BOSONIC_QUARTIC.is_dir():
        errors.append(f"missing bosonic quartic owner: {describe(BOSONIC_QUARTIC)}")
        return

    # Thermal direction is graph-owned. The exact umbrella import is a source-topology rule because
    # the umbrella intentionally shares the same module prefix as its semantic descendants.
    for path in lean_files(BOSONIC_QUARTIC):
        rel = path.relative_to(BOSONIC_QUARTIC)
        if rel.parts and rel.parts[0] == "Thermal":
            continue
        for line_no, imported in numbered_imports(path):
            if imported == BOSONIC_QUARTIC_PREFIX:
                errors.append(
                    "bosonic quartic semantics imports umbrella: "
                    f"{describe(path)}:{line_no}: `{imported}`"
                )


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_bosonic_umbrella_boundary(errors)
    return finish_audit(
        errors,
        failure_heading="Diagrammatics layer architecture audit failed:",
        success_message="Diagrammatics layer architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
