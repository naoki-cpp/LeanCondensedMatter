from __future__ import annotations

from pathlib import Path

from architecture_audit_common import finish_audit, lean_imports, relative as relative_to, repository_root

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
LINEAR_RESPONSE = QUANTUM / "LinearResponse"
FREE_DYNAMICS = LINEAR_RESPONSE / "FreeDynamics.lean"
CONSERVATION = LINEAR_RESPONSE / "ConservationLaws.lean"
DENSITY_EXPECTATION = LINEAR_RESPONSE / "DensityExpectation.lean"
DENSITY_BASIC = QUANTUM / "DensityOperator" / "Basic.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
CONSERVATION_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws"
PICTURE_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"
DENSITY_EXPECTATION_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation"


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def main() -> int:
    errors: list[str] = []

    for path in (FREE_DYNAMICS, CONSERVATION, DENSITY_EXPECTATION, DENSITY_BASIC):
        if not path.exists():
            errors.append(f"missing bounded conservation boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory conservation-law audit failed:",
            success_message="QuantumTheory conservation-law audit passed.",
        )

    # Hamiltonian typing, dimension independence, and derivative independence are compiled contracts.
    if CONSERVATION_MODULE not in lean_imports(ROOT_UMBRELLA):
        errors.append(
            "QuantumTheory public umbrella must expose bounded conservation laws: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    conservation_imports = lean_imports(CONSERVATION)
    for required_import in (PICTURE_MODULE, DENSITY_EXPECTATION_MODULE):
        if required_import not in conservation_imports:
            errors.append(
                f"conservation laws must import `{required_import}` in {relative(CONSERVATION)}"
            )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory conservation-law audit failed:",
        success_message="QuantumTheory conservation-law audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
