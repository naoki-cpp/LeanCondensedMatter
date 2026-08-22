from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    require_files,
    require_import,
    repository_root,
    strip_lean_comments,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ANALYSIS_OPERATOR = LEAN / "Analysis" / "Operator" / "LinearCommutator.lean"
SYMMETRIZED_PRODUCT = LEAN / "Analysis" / "Operator" / "SymmetrizedProduct.lean"
CURRENT_REPRESENTATION = LEAN / "Analysis" / "Calculus" / "CurrentRepresentation.lean"
BALANCE_LAW = LEAN / "Analysis" / "Calculus" / "BalanceLaw.lean"
SYMMETRIC_LOCALIZATION = LEAN / "Analysis" / "Calculus" / "SymmetricLocalization.lean"
QUANTUM_CURRENT = LEAN / "QuantumTheory" / "ConservationLaw"
SINGLE_PARTICLE_LOCALIZED_TRANSPORT = LEAN / "QuantumMechanics" / "SingleParticle" / "LocalizedTransport.lean"
SINGLE_PARTICLE_SYMMETRIZED_VELOCITY = LEAN / "QuantumMechanics" / "SingleParticle" / "SymmetrizedVelocityCurrent.lean"
SINGLE_PARTICLE_CONVENTIONAL = LEAN / "QuantumMechanics" / "SingleParticle" / "ConventionalCurrent.lean"
SINGLE_PARTICLE_SCHWARTZ = LEAN / "QuantumMechanics" / "SingleParticle" / "Continuum" / "Continuity" / "SchwartzCurrent1D.lean"
SINGLE_PARTICLE_SPIN = LEAN / "QuantumMechanics" / "SingleParticle" / "Continuum" / "Continuity" / "SchwartzSpinCurrent1D.lean"
FERMIONIC_FIELD_BRIDGE = LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity.lean"
BOUNDED_ONE_BODY_RESPONSE = LEAN / "SecondQuantization" / "Fermionic" / "Transport" / "BoundedOneBodyResponse.lean"
CONVENTIONAL_RESPONSE = LEAN / "SecondQuantization" / "Fermionic" / "Transport" / "ConventionalCurrentResponse.lean"
QUANTUM_UMBRELLA = LEAN / "QuantumTheory" / "ConservationLaw.lean"
TRANSPORT_UMBRELLA = LEAN / "SecondQuantization" / "Fermionic" / "Transport.lean"


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def code(path: Path) -> str:
    return strip_lean_comments(path.read_text(encoding="utf-8"))


def require_owner_import(errors: list[str], path: Path, imported: str) -> None:
    require_import(errors, path, imported, root=ROOT, description="architecture owner")


def main() -> int:
    errors: list[str] = []

    required = (
        ANALYSIS_OPERATOR,
        SYMMETRIZED_PRODUCT,
        CURRENT_REPRESENTATION,
        BALANCE_LAW,
        SYMMETRIC_LOCALIZATION,
        SINGLE_PARTICLE_LOCALIZED_TRANSPORT,
        SINGLE_PARTICLE_SYMMETRIZED_VELOCITY,
        SINGLE_PARTICLE_CONVENTIONAL,
        SINGLE_PARTICLE_SCHWARTZ,
        SINGLE_PARTICLE_SPIN,
        FERMIONIC_FIELD_BRIDGE,
        BOUNDED_ONE_BODY_RESPONSE,
        CONVENTIONAL_RESPONSE,
        QUANTUM_UMBRELLA,
        TRANSPORT_UMBRELLA,
    )
    require_files(errors, required, root=ROOT, description="generalized-current architecture owner")

    if errors:
        return finish_audit(
            errors,
            failure_heading="Generalized-current architecture audit failed:",
            success_message="Generalized-current architecture audit passed.",
        )

    require_owner_import(errors, BALANCE_LAW, "LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation")
    require_owner_import(errors, SYMMETRIC_LOCALIZATION, "LeanCondensedMatter.Analysis.Calculus.BalanceLaw")
    require_owner_import(errors, SYMMETRIC_LOCALIZATION, "LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct")

    symmetrized_code = code(SYMMETRIZED_PRODUCT)
    for token in ("symmetrizedProduct_nested", "linearCommutator"):
        if token not in symmetrized_code:
            errors.append(
                f"{relative(SYMMETRIZED_PRODUCT)} must own generic noncommutative symmetrization algebra `{token}`"
            )

    forbidden_quantum_localization_tokens = (
        "localizedQuantity",
        "localizationCommutatorFunctional",
        "transportFunctional",
        "sourceFunctional",
        "symmetrizedProductRightLinear",
    )
    for path in sorted(QUANTUM_CURRENT.glob("*.lean")):
        quantum_code = code(path)
        for token in forbidden_quantum_localization_tokens:
            if token in quantum_code:
                errors.append(
                    "QuantumTheory.ConservationLaw must not own symmetric-localization semantics: "
                    f"found `{token}` in {relative(path)}"
                )

    require_owner_import(errors, SINGLE_PARTICLE_LOCALIZED_TRANSPORT, "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization")
    require_owner_import(errors, SINGLE_PARTICLE_LOCALIZED_TRANSPORT, "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution")
    if "conventionalCurrent" in code(SINGLE_PARTICLE_LOCALIZED_TRANSPORT):
        errors.append(
            f"{relative(SINGLE_PARTICLE_LOCALIZED_TRANSPORT)} must not make conventional-current terminology fundamental"
        )

    require_owner_import(errors, SINGLE_PARTICLE_SYMMETRIZED_VELOCITY, "LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport")
    neutral_code = code(SINGLE_PARTICLE_SYMMETRIZED_VELOCITY)
    for token in (
        "symmetrizedVelocityCurrent",
        "symmetrizedVelocityTransport_decomposition",
        "symmetrizedVelocityCurrentRepresentation",
    ):
        if token not in neutral_code:
            errors.append(
                f"{relative(SINGLE_PARTICLE_SYMMETRIZED_VELOCITY)} must expose neutral current representation `{token}`"
            )
    if "conventionalCurrent" in neutral_code:
        errors.append(
            f"{relative(SINGLE_PARTICLE_SYMMETRIZED_VELOCITY)} must remain neutral about conventional-current terminology"
        )

    require_owner_import(errors, SINGLE_PARTICLE_CONVENTIONAL, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")
    conventional_code = code(SINGLE_PARTICLE_CONVENTIONAL)
    if "symmetrizedVelocityCurrent" not in conventional_code:
        errors.append(
            f"{relative(SINGLE_PARTICLE_CONVENTIONAL)} must delegate to the neutral symmetrized-velocity representation"
        )
    for forbidden in (
        "def heisenbergLocalizationFunctional",
        "def heisenbergTransportFunctional",
        "def operatorLocalCurrentPairing",
        "def velocityLocalizationFlux",
    ):
        if forbidden in conventional_code:
            errors.append(
                f"{relative(SINGLE_PARTICLE_CONVENTIONAL)} must not own generic transport machinery `{forbidden}`"
            )

    require_owner_import(errors, SINGLE_PARTICLE_SCHWARTZ, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")
    require_owner_import(errors, SINGLE_PARTICLE_SPIN, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")

    require_owner_import(errors, FERMIONIC_FIELD_BRIDGE, "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization")
    bridge_code = code(FERMIONIC_FIELD_BRIDGE)
    if "AlgebraicFock.dGamma" not in bridge_code:
        errors.append(f"{relative(FERMIONIC_FIELD_BRIDGE)} must remain an explicit dGamma bridge")

    require_owner_import(errors, CONVENTIONAL_RESPONSE, "LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct")
    require_owner_import(errors, CONVENTIONAL_RESPONSE, "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse")

    quantum_imports = lean_imports(QUANTUM_UMBRELLA)
    expected_quantum_imports = (
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution",
    )
    if quantum_imports != expected_quantum_imports:
        errors.append(
            f"{relative(QUANTUM_UMBRELLA)} must expose only the abstract Heisenberg owner; "
            f"found: {', '.join(quantum_imports)}"
        )

    require_owner_import(errors, TRANSPORT_UMBRELLA, "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedOneBodyResponse")
    require_owner_import(errors, TRANSPORT_UMBRELLA, "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConventionalCurrentResponse")

    return finish_audit(
        errors,
        failure_heading="Generalized-current architecture audit failed:",
        success_message="Generalized-current architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
