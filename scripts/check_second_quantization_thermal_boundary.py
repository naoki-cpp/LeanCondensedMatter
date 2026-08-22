from __future__ import annotations

from architecture_audit_common import finish_audit, lean_files, numbered_lines, repository_root

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"
FERMIONIC = SQ / "Fermionic"
COMPLETED = FERMIONIC / "CompletedSpace"
COMPLETED_UMBRELLA = FERMIONIC / "CompletedSpace.lean"
THERMAL = FERMIONIC / "Thermal"
THERMAL_UMBRELLA = FERMIONIC / "Thermal.lean"

MOVED_FROM_COMPLETED = (
    "FreeGibbs",
    "GibbsLadderIntertwining",
    "ThermalLadder",
    "ThermalPeel",
    "ThermalPeelIndexed",
    "ThermalKMS",
    "ThermalFirstPair",
    "ThermalRecursion",
    "FreeGibbsSummability",
    "GibbsModeTruncation",
    "GibbsModeTruncationExpectation",
    "UnboundedExpectation",
)

FERMIONIC_THERMAL_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal"
)
FINITE_THERMAL_COMPAT_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteThermalCompatibility"
)
UNBOUNDED_THERMAL_IMPORT = (
    "import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.UnboundedExpectation"
)


def main() -> int:
    errors: list[str] = []

    for stem in MOVED_FROM_COMPLETED:
        old_path = COMPLETED / f"{stem}.lean"
        if old_path.exists():
            errors.append(
                f"thermal theory returned to CompletedSpace: {old_path.relative_to(ROOT)}"
            )

    for path in lean_files(COMPLETED):
        for line_no, line in numbered_lines(path):
            if line.strip().startswith(FERMIONIC_THERMAL_IMPORT):
                errors.append(
                    "CompletedSpace imports Fermionic.Thermal: "
                    f"{path.relative_to(ROOT)}:{line_no}: {line.strip()}"
                )

    completed_umbrella = COMPLETED_UMBRELLA.read_text(encoding="utf-8")
    if FERMIONIC_THERMAL_IMPORT in completed_umbrella:
        errors.append("Fermionic.CompletedSpace umbrella must not export Fermionic.Thermal")
    if FINITE_THERMAL_COMPAT_IMPORT in completed_umbrella:
        errors.append(
            "Fermionic.CompletedSpace umbrella must not export finite thermal compatibility"
        )

    unbounded = THERMAL / "UnboundedExpectation.lean"
    if not unbounded.exists():
        errors.append("missing Fermionic/Thermal/UnboundedExpectation.lean")
    else:
        for line_no, line in numbered_lines(unbounded):
            if "Fermionic.CompletedSpace" in line and line.strip().startswith("import "):
                errors.append(
                    "unbounded Gibbs expectation regained completed-space dependency: "
                    f"{unbounded.relative_to(ROOT)}:{line_no}: {line.strip()}"
                )

    thermal_umbrella = THERMAL_UMBRELLA.read_text(encoding="utf-8")
    if UNBOUNDED_THERMAL_IMPORT not in thermal_umbrella:
        errors.append("Fermionic.Thermal umbrella must export UnboundedExpectation")

    return finish_audit(
        errors,
        failure_heading="SecondQuantization thermal-boundary audit failed:",
        success_message="SecondQuantization thermal-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
