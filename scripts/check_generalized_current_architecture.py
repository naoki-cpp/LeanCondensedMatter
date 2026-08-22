from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    require_files,
    require_import,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ANALYSIS_OPERATOR = LEAN / "Analysis" / "Operator" / "LinearCommutator.lean"
SYMMETRIZED_PRODUCT = LEAN / "Analysis" / "Operator" / "SymmetrizedProduct.lean"
CURRENT_REPRESENTATION = LEAN / "Analysis" / "Calculus" / "CurrentRepresentation.lean"
BALANCE_LAW = LEAN / "Analysis" / "Calculus" / "BalanceLaw.lean"
SYMMETRIC_LOCALIZATION = LEAN / "Analysis" / "Calculus" / "SymmetricLocalization.lean"
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

    # Keep only durable source topology here. The old helper-name/body snapshots were implementation
    # history rather than stable architecture contracts; semantic invariants belong in typed Lean
    # declarations when they need explicit CI protection.
    require_owner_import(errors, BALANCE_LAW, "LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation")
    require_owner_import(errors, SYMMETRIC_LOCALIZATION, "LeanCondensedMatter.Analysis.Calculus.BalanceLaw")
    require_owner_import(errors, SYMMETRIC_LOCALIZATION, "LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct")
    require_owner_import(errors, SINGLE_PARTICLE_LOCALIZED_TRANSPORT, "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization")
    require_owner_import(errors, SINGLE_PARTICLE_LOCALIZED_TRANSPORT, "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution")
    require_owner_import(errors, SINGLE_PARTICLE_SYMMETRIZED_VELOCITY, "LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport")
    require_owner_import(errors, SINGLE_PARTICLE_CONVENTIONAL, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")
    require_owner_import(errors, SINGLE_PARTICLE_SCHWARTZ, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")
    require_owner_import(errors, SINGLE_PARTICLE_SPIN, "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent")
    require_owner_import(errors, FERMIONIC_FIELD_BRIDGE, "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization")
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
