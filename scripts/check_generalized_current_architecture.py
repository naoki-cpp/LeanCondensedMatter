from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ANALYSIS_OPERATOR = LEAN / "Analysis" / "Operator" / "LinearCommutator.lean"
SYMMETRIZED_PRODUCT = LEAN / "Analysis" / "Operator" / "SymmetrizedProduct.lean"
CURRENT_REPRESENTATION = LEAN / "Analysis" / "Calculus" / "CurrentRepresentation.lean"
BALANCE_LAW = LEAN / "Analysis" / "Calculus" / "BalanceLaw.lean"
SYMMETRIC_LOCALIZATION = LEAN / "Analysis" / "Calculus" / "SymmetricLocalization.lean"
QUANTUM_CURRENT = LEAN / "QuantumTheory" / "ConservationLaw"
SINGLE_PARTICLE_LOCALIZED_TRANSPORT = (
    LEAN / "QuantumMechanics" / "SingleParticle" / "LocalizedTransport.lean"
)
SINGLE_PARTICLE_SYMMETRIZED_VELOCITY = (
    LEAN / "QuantumMechanics" / "SingleParticle" / "SymmetrizedVelocityCurrent.lean"
)
SINGLE_PARTICLE_CONVENTIONAL = (
    LEAN / "QuantumMechanics" / "SingleParticle" / "ConventionalCurrent.lean"
)
SINGLE_PARTICLE_SCHWARTZ = (
    LEAN
    / "QuantumMechanics"
    / "SingleParticle"
    / "Continuum"
    / "Continuity"
    / "SchwartzCurrent1D.lean"
)
SINGLE_PARTICLE_SPIN = (
    LEAN
    / "QuantumMechanics"
    / "SingleParticle"
    / "Continuum"
    / "Continuity"
    / "SchwartzSpinCurrent1D.lean"
)
FERMIONIC_FIELD_BRIDGE = (
    LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity.lean"
)
BOUNDED_RESPONSE = (
    LEAN / "SecondQuantization" / "Fermionic" / "Transport" / "BoundedCurrentResponse.lean"
)
CONVENTIONAL_RESPONSE = (
    LEAN / "SecondQuantization" / "Fermionic" / "Transport" / "ConventionalCurrentResponse.lean"
)
QUANTUM_UMBRELLA = LEAN / "QuantumTheory" / "ConservationLaw.lean"
FIELD_UMBRELLA = LEAN / "SecondQuantization" / "Fermionic" / "Field.lean"
TRANSPORT_UMBRELLA = LEAN / "SecondQuantization" / "Fermionic" / "Transport.lean"

OLD_CURRENT_OWNERS = (
    LEAN / "Analysis" / "Calculus" / "OneBodyBalance.lean",
    LEAN / "QuantumTheory" / "ConservationLaw" / "CurrentRepresentation.lean",
    LEAN / "QuantumTheory" / "ConservationLaw" / "HeisenbergTransport.lean",
    LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity" / "CurrentRepresentation.lean",
    LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity" / "ConventionalCurrent.lean",
    LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity" / "SchwartzCurrent1D.lean",
    LEAN / "SecondQuantization" / "Fermionic" / "Field" / "GeneralizedQuantity" / "SchwartzSpinCurrent1D.lean",
    LEAN / "QuantumTheory" / "ConservationLaw" / "ConventionalCurrent.lean",
    LEAN / "QuantumTheory" / "ConservationLaw" / "SchwartzCurrent1D.lean",
    LEAN / "QuantumTheory" / "ConservationLaw" / "SchwartzSpinCurrent1D.lean",
)

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)", re.MULTILINE)


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def code(path: Path) -> str:
    return strip_lean_comments(path.read_text(encoding="utf-8"))


def imports(path: Path) -> tuple[str, ...]:
    return tuple(IMPORT_RE.findall(code(path)))


def require_exists(errors: list[str], path: Path) -> None:
    if not path.exists():
        errors.append(f"missing generalized-current architecture owner: {relative(path)}")


def forbid_import_prefixes(
    errors: list[str], path: Path, prefixes: tuple[str, ...], description: str
) -> None:
    for imported in imports(path):
        if imported.startswith(prefixes):
            errors.append(
                f"{description}: {relative(path)} imports forbidden downstream module `{imported}`"
            )


def require_import(errors: list[str], path: Path, imported: str) -> None:
    if imported not in imports(path):
        errors.append(f"{relative(path)} must import canonical owner `{imported}`")


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
        BOUNDED_RESPONSE,
        CONVENTIONAL_RESPONSE,
        QUANTUM_UMBRELLA,
        FIELD_UMBRELLA,
        TRANSPORT_UMBRELLA,
    )
    for path in required:
        require_exists(errors, path)
    for path in OLD_CURRENT_OWNERS:
        if path.exists():
            errors.append(f"obsolete current owner must stay removed: {relative(path)}")

    if errors:
        return finish_audit(
            errors,
            failure_heading="Generalized-current architecture audit failed:",
            success_message="Generalized-current architecture audit passed.",
        )

    # Pure algebra, abstract balance/current semantics, and the algebraic symmetric-localization
    # realization stay upstream of quantum dynamics and particle statistics.
    for path in (
        ANALYSIS_OPERATOR,
        SYMMETRIZED_PRODUCT,
        CURRENT_REPRESENTATION,
        BALANCE_LAW,
        SYMMETRIC_LOCALIZATION,
    ):
        forbid_import_prefixes(
            errors,
            path,
            (
                "LeanCondensedMatter.QuantumTheory",
                "LeanCondensedMatter.QuantumMechanics",
                "LeanCondensedMatter.SecondQuantization",
            ),
            "analysis-level current semantics must remain representation-independent",
        )

    require_import(
        errors,
        BALANCE_LAW,
        "LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation",
    )
    require_import(
        errors,
        SYMMETRIC_LOCALIZATION,
        "LeanCondensedMatter.Analysis.Calculus.BalanceLaw",
    )
    require_import(
        errors,
        SYMMETRIC_LOCALIZATION,
        "LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct",
    )

    symmetrized_code = code(SYMMETRIZED_PRODUCT)
    for token in ("symmetrizedProduct_nested", "linearCommutator"):
        if token not in symmetrized_code:
            errors.append(
                f"{relative(SYMMETRIZED_PRODUCT)} must own generic noncommutative symmetrization algebra `{token}`"
            )

    # QuantumTheory supplies only abstract Heisenberg evolution. It must not regain a selected
    # localization map, transported one-body quantity, or a concrete current realization.
    forbidden_quantum_localization_tokens = (
        "localizedQuantity",
        "localizationCommutatorFunctional",
        "transportFunctional",
        "sourceFunctional",
        "symmetrizedProductRightLinear",
    )
    for path in sorted(QUANTUM_CURRENT.glob("*.lean")):
        forbid_import_prefixes(
            errors,
            path,
            (
                "LeanCondensedMatter.QuantumMechanics",
                "LeanCondensedMatter.SecondQuantization",
            ),
            "QuantumTheory.ConservationLaw must remain free of concrete kinematics and particle statistics",
        )
        quantum_code = code(path)
        for token in forbidden_quantum_localization_tokens:
            if token in quantum_code:
                errors.append(
                    "QuantumTheory.ConservationLaw must not own symmetric-localization semantics: "
                    f"found `{token}` in {relative(path)}"
                )

    # First-quantized localized transport owns Heisenberg/localizer/flux machinery without choosing
    # a particular current-density formula.
    require_import(
        errors,
        SINGLE_PARTICLE_LOCALIZED_TRANSPORT,
        "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization",
    )
    require_import(
        errors,
        SINGLE_PARTICLE_LOCALIZED_TRANSPORT,
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution",
    )
    localized_transport_code = code(SINGLE_PARTICLE_LOCALIZED_TRANSPORT)
    if "conventionalCurrent" in localized_transport_code:
        errors.append(
            f"{relative(SINGLE_PARTICLE_LOCALIZED_TRANSPORT)} must not make conventional-current terminology fundamental"
        )

    # A distinguished velocity may select the Hermitian density 1/2 {v,m}, but only as one local
    # current-density representation of the already-defined transport functional.
    require_import(
        errors,
        SINGLE_PARTICLE_SYMMETRIZED_VELOCITY,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.LocalizedTransport",
    )
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

    # The historical conventional-current name is a thin compatibility layer only.
    require_import(
        errors,
        SINGLE_PARTICLE_CONVENTIONAL,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent",
    )
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

    require_import(
        errors,
        SINGLE_PARTICLE_SCHWARTZ,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent",
    )
    require_import(
        errors,
        SINGLE_PARTICLE_SPIN,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent",
    )
    for path in (
        SINGLE_PARTICLE_LOCALIZED_TRANSPORT,
        SINGLE_PARTICLE_SYMMETRIZED_VELOCITY,
        SINGLE_PARTICLE_CONVENTIONAL,
        SINGLE_PARTICLE_SCHWARTZ,
        SINGLE_PARTICLE_SPIN,
    ):
        forbid_import_prefixes(
            errors,
            path,
            ("LeanCondensedMatter.SecondQuantization",),
            "single-particle current realizations must remain upstream of particle statistics",
        )

    # The fermionic field module is a dGamma bridge over the shared Analysis realization, not a
    # current owner and not a client of concrete first-quantized mechanics.
    require_import(
        errors,
        FERMIONIC_FIELD_BRIDGE,
        "LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization",
    )
    bridge_code = code(FERMIONIC_FIELD_BRIDGE)
    bridge_imports = imports(FERMIONIC_FIELD_BRIDGE)
    if "AlgebraicFock.dGamma" not in bridge_code:
        errors.append(
            f"{relative(FERMIONIC_FIELD_BRIDGE)} must remain an explicit dGamma bridge"
        )
    if any(
        imported.startswith("LeanCondensedMatter.QuantumMechanics")
        or "ConventionalCurrent" in imported
        or "SchwartzCurrent" in imported
        for imported in bridge_imports
    ):
        errors.append(
            f"{relative(FERMIONIC_FIELD_BRIDGE)} must not regain concrete current-representation ownership"
        )

    # Generic bounded response remains independent of conventional-current machinery. The
    # conventional adapter needs only the pure symmetrized-product algebra.
    for imported in imports(BOUNDED_RESPONSE):
        if "ConventionalCurrent" in imported:
            errors.append(
                f"{relative(BOUNDED_RESPONSE)} must not import conventional-current machinery: `{imported}`"
            )
    require_import(
        errors,
        CONVENTIONAL_RESPONSE,
        "LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct",
    )
    require_import(
        errors,
        CONVENTIONAL_RESPONSE,
        "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedCurrentResponse",
    )

    # The QuantumTheory umbrella exposes only the abstract Heisenberg owner.
    quantum_umbrella_imports = imports(QUANTUM_UMBRELLA)
    require_import(
        errors,
        QUANTUM_UMBRELLA,
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution",
    )
    for retired in (
        "CurrentRepresentation",
        "HeisenbergTransport",
        "ConventionalCurrent",
        "SchwartzCurrent1D",
        "SchwartzSpinCurrent1D",
    ):
        if any(retired in imported for imported in quantum_umbrella_imports):
            errors.append(
                f"{relative(QUANTUM_UMBRELLA)} must not re-export retired conservation leaf `{retired}`"
            )

    field_imports = imports(FIELD_UMBRELLA)
    for retired in (
        "CurrentRepresentation",
        "ConventionalCurrent",
        "SchwartzCurrent1D",
        "SchwartzSpinCurrent1D",
    ):
        if any(retired in imported for imported in field_imports):
            errors.append(
                f"{relative(FIELD_UMBRELLA)} must not re-export retired Field transport leaf `{retired}`"
            )
    require_import(
        errors,
        TRANSPORT_UMBRELLA,
        "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedCurrentResponse",
    )
    require_import(
        errors,
        TRANSPORT_UMBRELLA,
        "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConventionalCurrentResponse",
    )

    return finish_audit(
        errors,
        failure_heading="Generalized-current architecture audit failed:",
        success_message="Generalized-current architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
