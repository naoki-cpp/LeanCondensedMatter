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
DENSITY_BASIC = QUANTUM / "DensityOperator" / "Basic.lean"
ROOT_UMBRELLA = ROOT / "LeanCondensedMatter.lean"
CONSERVATION_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws"
)
PICTURE_IMPORT = (
    "import LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence"
)

REQUIRED_DECLARATIONS = (
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
    "noncomputable def DensityOperator.toNormalizedExpectation",
    "theorem DensityOperator.toNormalizedExpectation_apply",
    "theorem isStationary_toNormalizedExpectation_of_commute_hamiltonian",
)

CANONICAL_NAMES = tuple(declaration.split()[-1] for declaration in REQUIRED_DECLARATIONS)


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def declaration_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{re.escape(name)}\b",
        re.MULTILINE,
    )


def main() -> int:
    errors: list[str] = []

    for path in (CONSERVATION, DENSITY_BASIC):
        if not path.exists():
            errors.append(f"missing bounded conservation boundary file: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="QuantumTheory conservation-law audit failed:",
            success_message="QuantumTheory conservation-law audit passed.",
        )

    conservation_code = strip_lean_comments(CONSERVATION.read_text(encoding="utf-8"))
    normalized = " ".join(conservation_code.split())
    density_code = strip_lean_comments(DENSITY_BASIC.read_text(encoding="utf-8"))
    root_code = ROOT_UMBRELLA.read_text(encoding="utf-8")

    for declaration in REQUIRED_DECLARATIONS:
        if declaration not in conservation_code:
            errors.append(
                f"missing conservation declaration `{declaration}` in {relative(CONSERVATION)}"
            )

    if CONSERVATION_IMPORT not in root_code:
        errors.append(
            "root import surface must expose bounded conservation laws: "
            f"{relative(ROOT_UMBRELLA)}"
        )

    if PICTURE_IMPORT not in conservation_code:
        errors.append(
            "conservation laws must depend directly on picture equivalence rather than the later "
            f"equations-of-motion layer in {relative(CONSERVATION)}"
        )

    if "EquationsOfMotion" in conservation_code:
        errors.append(
            "algebraic conservation laws must not depend on equations of motion in "
            f"{relative(CONSERVATION)}"
        )

    for name in CANONICAL_NAMES:
        owners: list[Path] = []
        pattern = declaration_pattern(name)
        for path in lean_files(QUANTUM):
            code = strip_lean_comments(path.read_text(encoding="utf-8"))
            if pattern.search(code):
                owners.append(path)
        if owners != [CONSERVATION]:
            rendered = ", ".join(relative(path) for path in owners) or "<none>"
            errors.append(
                f"canonical declaration `{name}` must be owned exactly once by "
                f"{relative(CONSERVATION)}; found: {rendered}"
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

    required_boundaries = (
        "Commute system.hamiltonian A",
        "freePropagator_neg_mul system t",
        "freePropagator_mul_neg system t",
        "expValue_evolveState_eq_heisenberg system",
        "expectation_evolveDensityOperator_eq_heisenberg system",
        "DensityOperator.ext",
        "IsStationary system ρ.toNormalizedExpectation",
    )
    for boundary in required_boundaries:
        if boundary not in normalized:
            errors.append(
                f"bounded conservation implementation must retain `{boundary}` in "
                f"{relative(CONSERVATION)}"
            )

    for path, code in ((CONSERVATION, conservation_code), (DENSITY_BASIC, density_code)):
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
