from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import finish_audit, lean_files, numbered_lines, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
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

OLD_FIELD_MODULE = re.compile(
    r"LeanCondensedMatter\.SecondQuantization\.Fermionic\.Field\."
    r"(?:" + "|".join(map(re.escape, TRANSPORT_NAMES)) + r"|Validation\.)"
)

VALIDATION_IMPORT = re.compile(
    r"^\s*import\s+LeanCondensedMatter\.SecondQuantization\.Fermionic\.Validation(?:\.|\s|$)"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def check_layout(errors: list[str]) -> None:
    required = [FERMIONIC / "Transport.lean", FERMIONIC / "Validation.lean"]
    required += [TRANSPORT / f"{name}.lean" for name in TRANSPORT_NAMES]
    required += [VALIDATION / f"{name}.lean" for name in VALIDATION_NAMES]
    for path in required:
        if not path.is_file():
            errors.append(f"missing fermionic transport/validation module: {rel(path)}")

    for name in TRANSPORT_NAMES:
        old = FIELD / f"{name}.lean"
        if old.exists():
            errors.append(f"obsolete Fermionic.Field transport module still exists: {rel(old)}")
    if (FIELD / "Validation").exists():
        errors.append("obsolete Fermionic.Field.Validation tree still exists")

    field_lean = {p.name for p in FIELD.glob("*.lean")}
    expected_field = {
        "ChargeDensity.lean",
        "ContinuumChargeDensity1D.lean",
        "ContinuumL2ChargeDensity1D.lean",
        "GeneralizedQuantity.lean",
    }
    unexpected = sorted(field_lean - expected_field)
    if unexpected:
        errors.append("Fermionic.Field still owns unrelated leaf modules: " + ", ".join(unexpected))


def check_namespaces(errors: list[str]) -> None:
    for path in lean_files(TRANSPORT):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"transport declaration remains in Field namespace: {rel(path)}")
        if "open SecondQuantization.Fermionic.Field" in code:
            errors.append(f"transport module still opens the obsolete Field owner: {rel(path)}")
    for path in lean_files(VALIDATION):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if "namespace Field" in code:
            errors.append(f"validation declaration remains in Field namespace: {rel(path)}")


def check_dependency_direction(errors: list[str]) -> None:
    # Validation is terminal: no public algebra/lattice/field/transport module may depend on it.
    upstream_roots = [FERMIONIC / "Algebra", FERMIONIC / "Lattice", FIELD, TRANSPORT]
    for root in upstream_roots:
        for path in lean_files(root):
            for line_no, line in numbered_lines(path):
                if VALIDATION_IMPORT.match(line):
                    errors.append(
                        f"upstream fermionic layer imports Validation: {rel(path)}:{line_no}: {line.strip()}"
                    )


def check_old_paths(errors: list[str]) -> None:
    for path in lean_files(ROOT / "LeanCondensedMatter"):
        for line_no, line in numbered_lines(path):
            if OLD_FIELD_MODULE.search(line):
                errors.append(f"old Fermionic.Field transport/validation path remains: {rel(path)}:{line_no}: {line.strip()}")


def main() -> int:
    errors: list[str] = []
    check_layout(errors)
    check_namespaces(errors)
    check_dependency_direction(errors)
    check_old_paths(errors)
    return finish_audit(
        errors,
        failure_heading="Fermionic transport/validation boundary audit failed:",
        success_message="Fermionic transport/validation boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
