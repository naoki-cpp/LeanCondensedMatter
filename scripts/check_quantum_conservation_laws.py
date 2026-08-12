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
LINEAR_RESPONSE = QUANTUM / "LinearResponse"
FREE_DYNAMICS = LINEAR_RESPONSE / "FreeDynamics.lean"
CONSERVATION = LINEAR_RESPONSE / "ConservationLaws.lean"
DENSITY_EXPECTATION = LINEAR_RESPONSE / "DensityExpectation.lean"
KUBO_FORMULA = LINEAR_RESPONSE / "KuboFormula.lean"
SOURCE_COUPLING = LINEAR_RESPONSE / "SourceCoupling.lean"
DENSITY_BASIC = QUANTUM / "DensityOperator" / "Basic.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
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

    for path in (
        FREE_DYNAMICS,
        CONSERVATION,
        DENSITY_EXPECTATION,
        KUBO_FORMULA,
        SOURCE_COUPLING,
        DENSITY_BASIC,
    ):
        if not path.exists():
            errors.append(f"missing bounded conservation boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory conservation-law audit failed:",
            success_message="QuantumTheory conservation-law audit passed.",
        )

    free_dynamics_code = strip_lean_comments(FREE_DYNAMICS.read_text(encoding="utf-8"))
    free_dynamics_normalized = " ".join(free_dynamics_code.split())
    conservation_code = strip_lean_comments(CONSERVATION.read_text(encoding="utf-8"))
    conservation_normalized = " ".join(conservation_code.split())
    density_expectation_code = strip_lean_comments(
        DENSITY_EXPECTATION.read_text(encoding="utf-8")
    )
    density_expectation_normalized = " ".join(density_expectation_code.split())
    kubo_code = strip_lean_comments(KUBO_FORMULA.read_text(encoding="utf-8"))
    kubo_normalized = " ".join(kubo_code.split())
    source_code = strip_lean_comments(SOURCE_COUPLING.read_text(encoding="utf-8"))
    source_normalized = " ".join(source_code.split())
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

    if "hamiltonian : Observable H" not in free_dynamics_normalized:
        errors.append(
            "bounded free systems must store the Hamiltonian in the canonical observable type: "
            f"{relative(FREE_DYNAMICS)}"
        )
    for retired_boundary in (
        "hamiltonian : H →L[ℂ] H",
        "hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian",
    ):
        if retired_boundary in free_dynamics_normalized:
            errors.append(
                "bounded free systems must not split observable data into parallel fields; found "
                f"`{retired_boundary}` in {relative(FREE_DYNAMICS)}"
            )

    if CONSERVATION_IMPORT not in root_code:
        errors.append(
            "QuantumTheory public umbrella must expose bounded conservation laws: "
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

    for retired_wrapper in ("hamiltonianObservable", "coe_hamiltonianObservable"):
        if retired_wrapper in conservation_code:
            errors.append(
                "conservation laws must use `system.hamiltonian` directly rather than rewrapping "
                f"it as `{retired_wrapper}` in {relative(CONSERVATION)}"
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
        "Commute system.hamiltonian.1 A",
        "freePropagator_neg_mul",
        "expValue_evolveState_eq_heisenberg system",
        "expectation_evolveDensityOperator_eq_heisenberg system",
        "heisenbergEvolution_eq_self_of_commute_hamiltonian system A hA (-t)",
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

    downstream_boundaries = (
        (
            KUBO_FORMULA,
            kubo_normalized,
            "system ρ.toNormalizedExpectation hVself A hM hV ht hInt",
        ),
        (
            SOURCE_COUPLING,
            source_normalized,
            "system ρ.toNormalizedExpectation f hB A hM hV ht hInt",
        ),
    )
    for path, code, boundary in downstream_boundaries:
        if boundary not in code:
            errors.append(
                "density-state response specializations must reuse the canonical normalized "
                f"expectation bridge; missing `{boundary}` in {relative(path)}"
            )
        if "densityNormalizedExpectation" in code:
            errors.append(
                "retired local density expectation bridge must not be reintroduced in "
                f"{relative(path)}"
            )

    for path, code in (
        (FREE_DYNAMICS, free_dynamics_code),
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
