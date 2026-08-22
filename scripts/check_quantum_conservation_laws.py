from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files_matching,
    lean_imports,
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
DENSITY_BASIC = QUANTUM / "DensityOperator" / "Basic.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter" / "QuantumTheory.lean"
CONSERVATION_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws"
PICTURE_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"
DENSITY_EXPECTATION_MODULE = "LeanCondensedMatter.QuantumTheory.LinearResponse.DensityExpectation"

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
        owners = lean_files_matching(QUANTUM, declaration_pattern(name))
        if owners != [owner]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"canonical declaration `{name}` must be owned exactly once by "
                f"{relative(owner)}; found: {rendered}"
            )


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

    free_dynamics_code = strip_lean_comments(FREE_DYNAMICS.read_text(encoding="utf-8"))
    free_dynamics_normalized = " ".join(free_dynamics_code.split())
    conservation_code = strip_lean_comments(CONSERVATION.read_text(encoding="utf-8"))
    density_expectation_code = strip_lean_comments(DENSITY_EXPECTATION.read_text(encoding="utf-8"))
    density_code = strip_lean_comments(DENSITY_BASIC.read_text(encoding="utf-8"))

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

    if any("EquationsOfMotion" in imported for imported in conservation_imports):
        errors.append(
            "algebraic conservation laws must not depend on equations of motion in "
            f"{relative(CONSERVATION)}"
        )

    check_owned_declarations(errors, CONSERVATION_DECLARATIONS, CONSERVATION)
    check_owned_declarations(errors, DENSITY_EXPECTATION_DECLARATIONS, DENSITY_EXPECTATION)

    ext_owners = lean_files_matching(QUANTUM, declaration_pattern("DensityOperator.ext"))
    if ext_owners != [DENSITY_BASIC]:
        rendered = ", ".join(relative(path) for path in ext_owners) or "<none>"
        errors.append(
            "density-operator extensionality must be owned exactly once by "
            f"{relative(DENSITY_BASIC)}; found: {rendered}"
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
            "algebraic conservation laws must remain independent of derivative machinery in "
            f"{relative(CONSERVATION)}"
        )

    return finish_audit(
        errors,
        failure_heading="QuantumTheory conservation-law audit failed:",
        success_message="QuantumTheory conservation-law audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
