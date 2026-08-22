from __future__ import annotations

from architecture_audit_common import (
    ImportBoundary,
    check_import_boundaries,
    finish_audit,
    module_matches_prefix,
    numbered_imports,
    repository_root,
    require_files,
)

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC = SQ / "Fermionic"
COMPLETED = FERMIONIC / "CompletedSpace"
COMPLETED_UMBRELLA = FERMIONIC / "CompletedSpace.lean"
THERMAL = FERMIONIC / "Thermal"
THERMAL_UMBRELLA = FERMIONIC / "Thermal.lean"
UNBOUNDED_EXPECTATION = THERMAL / "UnboundedExpectation.lean"

COMMON_THERMAL_PREFIX = "LeanCondensedMatter.SecondQuantization.Common.Thermal"
FERMIONIC_THERMAL_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.Thermal"
BOSONIC_THERMAL_PREFIX = "LeanCondensedMatter.SecondQuantization.Bosonic.Thermal"
COMPLETED_PREFIX = "LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace"
UNBOUNDED_THERMAL_IMPORT = f"{FERMIONIC_THERMAL_PREFIX}.UnboundedExpectation"

DEPENDENCY_BOUNDARIES = (
    ImportBoundary(
        COMPLETED,
        (FERMIONIC_THERMAL_PREFIX,),
        "CompletedSpace representation infrastructure must remain upstream of Fermionic.Thermal",
    ),
)


def main() -> int:
    errors: list[str] = []

    require_files(
        errors,
        (COMPLETED_UMBRELLA, THERMAL_UMBRELLA, UNBOUNDED_EXPECTATION),
        root=ROOT,
        description="thermal/completed-space architecture owner",
    )
    if not COMPLETED.is_dir():
        errors.append(f"missing completed-space owner: {COMPLETED.relative_to(ROOT)}")
    if not THERMAL.is_dir():
        errors.append(f"missing fermionic thermal owner: {THERMAL.relative_to(ROOT)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="SecondQuantization thermal-boundary audit failed:",
            success_message="SecondQuantization thermal-boundary audit passed.",
        )

    check_import_boundaries(errors, DEPENDENCY_BOUNDARIES, root=ROOT)

    # The public representation umbrella exposes representation API only, never thermal theory.
    thermal_prefixes = (
        COMMON_THERMAL_PREFIX,
        FERMIONIC_THERMAL_PREFIX,
        BOSONIC_THERMAL_PREFIX,
    )
    for line_no, imported in numbered_imports(COMPLETED_UMBRELLA):
        if any(module_matches_prefix(imported, prefix) for prefix in thermal_prefixes):
            errors.append(
                "Fermionic.CompletedSpace umbrella exports thermal API: "
                f"{COMPLETED_UMBRELLA.relative_to(ROOT)}:{line_no}: {imported}"
            )

    # The generic unbounded diagonal expectation is thermal theory, not completed-space machinery.
    for line_no, imported in numbered_imports(UNBOUNDED_EXPECTATION):
        if module_matches_prefix(imported, COMPLETED_PREFIX):
            errors.append(
                "unbounded Gibbs expectation depends on CompletedSpace: "
                f"{UNBOUNDED_EXPECTATION.relative_to(ROOT)}:{line_no}: {imported}"
            )

    thermal_exports = {imported for _, imported in numbered_imports(THERMAL_UMBRELLA)}
    if UNBOUNDED_THERMAL_IMPORT not in thermal_exports:
        errors.append(
            "Fermionic.Thermal umbrella must export the unbounded Gibbs expectation owner"
        )

    return finish_audit(
        errors,
        failure_heading="SecondQuantization thermal-boundary audit failed:",
        success_message="SecondQuantization thermal-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
