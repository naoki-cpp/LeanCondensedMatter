from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    repository_root,
    require_files,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
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


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_layout(errors: list[str]) -> None:
    required = [FERMIONIC / "Transport.lean", FERMIONIC / "Validation.lean"]
    required += [TRANSPORT / f"{name}.lean" for name in TRANSPORT_NAMES]
    required += [VALIDATION / f"{name}.lean" for name in VALIDATION_NAMES]
    require_files(errors, required, root=ROOT, description="fermionic transport/validation owner")


def check_namespaces(errors: list[str]) -> None:
    # Import direction is owned by the shared scoped architecture DAG. These source guards remain
    # only until the path-owned subnamespace contracts are migrated to compiled metadata.
    for path in lean_files(TRANSPORT):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"transport declaration is outside its path-owned namespace: {rel(path)}")
    for path in lean_files(VALIDATION):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"validation declaration is outside its path-owned namespace: {rel(path)}")


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_namespaces(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic transport/validation boundary audit failed:",
        success_message="Fermionic transport/validation boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
