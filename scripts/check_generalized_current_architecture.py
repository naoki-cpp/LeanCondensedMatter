from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import finish_audit, repository_root, strip_lean_comments

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
ANALYSIS_OPERATOR = LEAN / "Analysis" / "Operator" / "LinearCommutator.lean"
ONE_BODY_BALANCE = LEAN / "Analysis" / "Calculus" / "OneBodyBalance.lean"
CURRENT_REPRESENTATION = LEAN / "Analysis" / "Calculus" / "CurrentRepresentation.lean"
QUANTUM_CURRENT = LEAN / "QuantumTheory" / "ConservationLaw"
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
        ONE_BODY_BALANCE,
        CURRENT_REPRESENTATION,
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

    # Generic algebra and one-body balance must remain upstream of all quantum and
    # second-quantized realizations.
    for path in (ANALYSIS_OPERATOR, ONE_BODY_BALANCE, CURRENT_REPRESENTATION):
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

    # Abstract quantum transport may depend on Analysis, but it must remain upstream
    # of both concrete single-particle kinematics and particle statistics.
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

    # A distinguished velocity and the conventional formula j^m = 1/2 {v,m} belong
    # to first-quantized mechanics, downstream of the abstract Heisenberg machinery.
    require_import(
        errors,
        SINGLE_PARTICLE_CONVENTIONAL,
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergTransport",
    )
    require_import(
        errors,
        SINGLE_PARTICLE_SCHWARTZ,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.ConventionalCurrent",
    )
    require_import(
        errors,
        SINGLE_PARTICLE_SPIN,
        "LeanCondensedMatter.QuantumMechanics.SingleParticle.ConventionalCurrent",
    )
    for path in (
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

    # The Fermionic Field owner is now a dGamma bridge, not a transport owner. The
    # dGamma implementation may arrive transitively through ChargeDensity, so inspect
    # the bridge semantics rather than requiring a direct AlgebraicFock import.
    bridge_code = code(FERMIONIC_FIELD_BRIDGE)
    bridge_imports = imports(FERMIONIC_FIELD_BRIDGE)
    if "AlgebraicFock.dGamma" not in bridge_code:
        errors.append(
            f"{relative(FERMIONIC_FIELD_BRIDGE)} must remain an explicit dGamma bridge"
        )
    if any(
        "ConventionalCurrent" in imported or "SchwartzCurrent" in imported
        for imported in bridge_imports
    ):
        errors.append(
            f"{relative(FERMIONIC_FIELD_BRIDGE)} must not regain concrete current-representation ownership"
        )

    # Generic bounded response must stay independent of conventional current machinery.
    for imported in imports(BOUNDED_RESPONSE):
        if "ConventionalCurrent" in imported:
            errors.append(
                f"{relative(BOUNDED_RESPONSE)} must not import conventional-current machinery: `{imported}`"
            )
    require_import(
        errors,
        CONVENTIONAL_RESPONSE,
        "LeanCondensedMatter.SecondQuantization.Fermionic.Transport.BoundedCurrentResponse",
    )

    # The QuantumTheory umbrella exposes only model-independent owners. Concrete
    # velocity/current realizations are deliberately not re-exported through it.
    require_import(
        errors,
        QUANTUM_UMBRELLA,
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.CurrentRepresentation",
    )
    require_import(
        errors,
        QUANTUM_UMBRELLA,
        "LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergTransport",
    )
    for retired in (
        "ConventionalCurrent",
        "SchwartzCurrent1D",
        "SchwartzSpinCurrent1D",
    ):
        if any(retired in imported for imported in imports(QUANTUM_UMBRELLA)):
            errors.append(
                f"{relative(QUANTUM_UMBRELLA)} must not re-export concrete current leaf `{retired}`"
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
