from __future__ import annotations

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
ALGEBRA = FERMIONIC / "Algebra"
LATTICE = FERMIONIC / "Lattice"
FIELD = FERMIONIC / "Field"
TRANSPORT = FERMIONIC / "Transport"
VALIDATION = FERMIONIC / "Validation"

TRANSPORT_NAMES = (
    "BoundedOneBodyResponse",
    "ConductivityNormalization",
    "FrequencyResponse",
    "GeometricCurrentResponse",
    "HarmonicSourceResponse",
    "InfiniteTimeFrequencyResponse",
    "KuboBastinSpectral",
    "KuboBastinTrace",
    "KuboGreenwood",
    "SpectralFrequencyResponse",
    "StaticKuboBastinResponse",
    "StationaryFrequencyResponse",
)

VALIDATION_NAMES = ("FiniteToys", "TwoLevelExplicit", "TwoSiteDimer")

ALGEBRA_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Algebra"
FIELD_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Field"
LATTICE_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Lattice"
TRANSPORT_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Transport"
VALIDATION_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Validation"

# Stable fermionic responsibility graph:
#
#   Algebra
#      ↓
#   Field   Lattice
#      \     /
#      Transport
#          ↓
#      Validation
#
# Field and Lattice are sibling realizations. Neither is allowed to depend on Transport/Validation,
# and reusable Algebra is upstream of all three realization/consumer layers.
DEPENDENCY_BOUNDARIES = (
    ImportBoundary(
        ALGEBRA,
        (FIELD_PREFIX, LATTICE_PREFIX, TRANSPORT_PREFIX, VALIDATION_PREFIX),
        "Fermionic.Algebra must remain upstream of realization and consumer layers",
    ),
    ImportBoundary(
        FIELD,
        (LATTICE_PREFIX, TRANSPORT_PREFIX, VALIDATION_PREFIX),
        "Fermionic.Field must remain an upstream side interface",
    ),
    ImportBoundary(
        LATTICE,
        (FIELD_PREFIX, TRANSPORT_PREFIX, VALIDATION_PREFIX),
        "Fermionic.Lattice must remain an upstream realization layer",
    ),
    ImportBoundary(
        TRANSPORT,
        (VALIDATION_PREFIX,),
        "Fermionic.Transport must remain upstream of Validation",
    ),
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_layout(errors: list[str]) -> None:
    required = [FERMIONIC / "Transport.lean", FERMIONIC / "Validation.lean"]
    required += [TRANSPORT / f"{name}.lean" for name in TRANSPORT_NAMES]
    required += [VALIDATION / f"{name}.lean" for name in VALIDATION_NAMES]
    require_files(errors, required, root=ROOT, description="fermionic transport/validation owner")


def check_namespaces(errors: list[str]) -> None:
    for path in lean_files(TRANSPORT):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"transport declaration is outside its path-owned namespace: {rel(path)}")
    for path in lean_files(VALIDATION):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"validation declaration is outside its path-owned namespace: {rel(path)}")


def check_dependency_direction(errors: list[str]) -> None:
    check_import_boundaries(errors, DEPENDENCY_BOUNDARIES, root=ROOT)


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_namespaces(errors)
    check_dependency_direction(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic transport/validation boundary audit failed:",
        success_message="Fermionic transport/validation boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
