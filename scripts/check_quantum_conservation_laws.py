from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    relative as relative_to,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
QUANTUM = ROOT / "LeanCondensedMatter" / "QuantumTheory"
CONSERVATION = QUANTUM / "LinearResponse" / "ConservationLaws.lean"
DENSITY_EXPECTATION = QUANTUM / "LinearResponse" / "DensityExpectation.lean"
DENSITY_BASIC = QUANTUM / "DensityOperator" / "Basic.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter.lean"
CONSERVATION_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws"
)
PICTURE_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"
)
DENSITY_EXPECTATION_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation"
)

CONSERVATION_DECLARATIONS = (
    "noncomputable def hamiltonianObservable",
    "theorem coe_hamiltonianObservable",
    "theorem commute_freePropagator_of_commute_hamiltonian",
    "theorem heisenbergEvolution_eq_self_of_commute_hamiltonian",
    "theorem heisenbergObservable_eq_self_of_commute_hamiltonian",
    "theorem expValue_evolveState_eq_of_commute_hamiltonian",
    "theorem observableExpValue_evolveState_eq_of_commute_hamiltonian",
    "theorem expectation_evolveDensityOperator_eq_of_commute_hamiltonian",
    "theorem observableExpectation_evolveDensityOperator_eq_of_commute_hamiltonian",
    "theorem expValue_hamiltonian_evolveState",
    "theorem observableExpValue_hamiltonian_evolveState",
    "theorem expectation_hamiltonian_evolveDensityOperator",
    "theorem observableExpectation_hamiltonian_evolveDensityOperator",
    "theorem unitaryConjugate_freePropagator_eq_self_of_commute_hamiltonian",
    "theorem evolveDensityOperator_eq_self_of_commute_hamiltonian",
    "theorem isStationary_toNormalizedExpectation_of_commute_hamiltonian",
)

DENSITY_EXPECTATION_DECLARATIONS = (
    "noncomputable def DensityOperator.toNormalizedExpectation",
    "theorem DensityOperator.toNormalizedExpectation_apply",
)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def declaration_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}\b",
        re.MULTILINE,
    )


def check_owned_declarations(
    errors: list[str], declarations: tuple[str, ...], owner: Path
) -> None:
    for declaration in declarations:
        name = declaration.split()[-1]
        owners: list[Path] = []
        pattern = declaration_pattern(name)
        for path in lean_files(QUANTUM):
            code = strip_lean_comments(path.read_text(encoding="utf-8"))
            if pattern.search(code):
                owners.append(path)
        if owners != [owner]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"canonical declaration `{name}` must be owned exactly once by "
                f"{relative(owner)}; found: {rendered}"
            )


def main() -> int:
    errors: list[str] = []

    for path in (CONSERVATION, DENSITY_EXPECTATION, DENSITY_BASIC):
        if not path.exists():
            errors.append(f"missing bounded conservation boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory conservation-law audit failed:",
            success_message="QuantumTheory conservation-law audit passed.",
        )

    conservation_code = strip_lean_comments(CONSERVATION.read_text(encoding="utf-8"))
    conservation_normalized = " ".join(conservation_code.split())
    density_expectation_code = strip_lean_comments(
        DENSITY_EXPECTATION.read_text(encoding="utf-8")
    )
    density_expectation_normalized = " ".join(density_expectation_code.split())
    density_code = strip_lean_comments(DENSITY_BASIC.read_text(encoding="utf-8"))
    root_code = ROOT_UMBRELLA.read_text(encoding="utf-8")

    for declaration in CONSERVATION_DECLARATIONS:
        if declaration not in conservation_code:
            errors.append(
                f"missing conservation declaration `{declaration}` in {relative(CONSERVATION)}"
            )

    for declaration in DENSITY_EXPECTATION_DECLARATIONS:
        if declaration not in density_expectation_code:
            errors.append(
                "missing density-expectation declaration "
                f"`{declaration}` in {relative(DENSITY_EXPECTATION)}"
            )

    if CONSERVATION_IMPORT not in root_code:
        errors.append(
            "root import surface must expose bounded conservation laws: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    for required_import in (PICTURE_IMPORT, DENSITY_EXPECTATION_IMPORT):
        if required_import not in conservation_code:
            errors.append(
                f"conservation laws must import `{required_import}` in {relative(CONSERVATION)}"
            )

    if "EquationsOfMotion" in conservation_code:
        errors.append(
            "algebraic conservation laws must not depend on equations of motion in "
            f"{relative(CONSERVATION)}"
        )

    check_owned_declarations(errors, CONSERVATION_DECLARATIONS, CONSERVATION)
    check_owned_declarations(
        errors, DENSITY_EXPECTATION_DECLARATIONS, DENSITY_EXPECTATION
    )

    ext_owners: list[Path] = []
    ext_pattern = declaration_pattern("DensityOperator.ext")
    for path in lean_files(QUANTUM):
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        if ext_pattern.search(code):
            ext_owners.append(path)
    if ext_owners != [DENSITY_BASIC]:
        rendered = ", ".join(relative(path) for path in ext_owners) or "<none>"
        errors.append(
            "density-operator extensionality must be owned exactly once by "
            f"{relative(DENSITY_BASIC)}; found: {rendered}"
        )

    conservation_boundaries = (
        "Commute system.hamiltonian A",
        "freePropagator_neg_mul system t",
        "freePropagator_mul_neg system t",
        "expValue_evolveState_eq_heisenberg system",
        "expectation_evolveDensityOperator_eq_heisenberg system",
        "DensityOperator.ext",
        "IsStationary system ρ.toNormalizedExpectation",
    )
    for boundary in conservation_boundaries:
        if boundary not in conservation_normalized:
            errors.append(
                f"bounded conservation implementation must retain `{boundary}` in "
                f"{relative(CONSERVATION)}"
            )

    density_expectation_boundaries = (
        "toContinuousLinearMap := ρ.expectation",
        "exact ρ.expectation_id",
    )
    for boundary in density_expectation_boundaries:
        if boundary not in density_expectation_normalized:
            errors.append(
                f"density expectation bridge must retain `{boundary}` in "
                f"{relative(DENSITY_EXPECTATION)}"
            )

    for path, code in (
        (CONSERVATION, conservation_code),
        (DENSITY_EXPECTATION, density_expectation_code),
        (DENSITY_BASIC, density_code),
    ):
        for finite_assumption in ("[FiniteDimensional", "[Fintype"):
            if finite_assumption in code:
                errors.append(
                    "bounded conservation laws must remain dimension-independent; found "
                    f"`{finite_assumption}` in {relative(path)}"
                )

    if "HasDerivAt" in conservation_code:
        errors.append(
            "conservation laws should use exact propagator and picture identities rather than "
            f"re-integrating derivatives in {relative(CONSERVATION)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory conservation-law audit failed:",
        success_message="QuantumTheory conservation-law audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
