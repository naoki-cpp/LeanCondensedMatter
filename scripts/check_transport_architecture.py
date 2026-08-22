from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    require_files,
    require_import,
    relative as relative_to,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
TRANSPORT = LEAN / "Transport"
LINEAR_RESPONSE = LEAN / "QuantumTheory" / "LinearResponse"
FERMIONIC_TRANSPORT = LEAN / "SecondQuantization" / "Fermionic" / "Transport"

NEUTRAL_OWNERS = (
    TRANSPORT / "ConductivityNormalization.lean",
    TRANSPORT / "FiniteConductivityTable.lean",
    TRANSPORT / "FiniteTrace.lean",
    TRANSPORT / "ResolventSpectral.lean",
    TRANSPORT / "FiniteKuboBastin.lean",
    TRANSPORT / "KuboBastinOccupation.lean",
    TRANSPORT / "KuboBastinCommonEnergy.lean",
    TRANSPORT / "GeneralizedStaticStreda.lean",
    TRANSPORT / "FiniteDisorder.lean",
    TRANSPORT / "FiniteDisorderResolvent.lean",
    TRANSPORT / "FiniteDisorderMoments.lean",
    TRANSPORT / "FiniteDisorderBorn.lean",
    TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
    TRANSPORT / "FiniteDisorderSCBA.lean",
)

ADIABATIC_RESPONSE_OWNERS = (
    LINEAR_RESPONSE / "AdiabaticSwitching.lean",
    LINEAR_RESPONSE / "HarmonicSource.lean",
    LINEAR_RESPONSE / "FiniteTimeAdiabatic.lean",
    LINEAR_RESPONSE / "InfiniteTimeAdiabatic.lean",
)

RETIRED_TRANSPORT_MODULES = (
    TRANSPORT / "System.lean",
    TRANSPORT / "LinearResponse.lean",
    TRANSPORT / "StredaResolventSpectral.lean",
    TRANSPORT / "StredaOccupation.lean",
    TRANSPORT / "StredaCommonKernel.lean",
)

RETIRED_FERMIONIC_TRANSPORT_MODULES = (
    FERMIONIC_TRANSPORT / "StredaOccupation.lean",
    FERMIONIC_TRANSPORT / "StredaCommonKernel.lean",
)

FERMIONIC_SPECIALIZATIONS = {
    FERMIONIC_TRANSPORT / "ConductivityNormalization.lean":
        "LeanCondensedMatter.Transport.Core.ConductivityNormalization",
    FERMIONIC_TRANSPORT / "FiniteConductivityTable.lean":
        "LeanCondensedMatter.Transport.Core.FiniteConductivityTable",
    FERMIONIC_TRANSPORT / "KuboBastinSpectral.lean":
        "LeanCondensedMatter.Transport.KuboBastin.Finite",
    FERMIONIC_TRANSPORT / "KuboBastinOccupation.lean":
        "LeanCondensedMatter.Transport.KuboBastin.Occupation",
    FERMIONIC_TRANSPORT / "KuboBastinCommonEnergy.lean":
        "LeanCondensedMatter.Transport.KuboBastin.CommonEnergy",
    FERMIONIC_TRANSPORT / "StaticKuboBastinResponse.lean":
        "LeanCondensedMatter.Transport.GeneralizedStaticStreda",
}


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def require_owner_import(errors: list[str], path: Path, imported: str) -> None:
    require_import(errors, path, imported, root=ROOT, description="transport specialization")


def main() -> int:
    errors: list[str] = []

    require_files(errors, NEUTRAL_OWNERS, root=ROOT, description="canonical transport owner")
    require_files(
        errors,
        ADIABATIC_RESPONSE_OWNERS,
        root=ROOT,
        description="canonical linear-response owner",
    )

    for path in RETIRED_TRANSPORT_MODULES:
        if path.exists():
            errors.append(
                f"{relative(path)} is retired and must not be reintroduced into generic Transport"
            )

    for path in RETIRED_FERMIONIC_TRANSPORT_MODULES:
        if path.exists():
            errors.append(
                f"{relative(path)} is retired and must not be reintroduced into fermionic Transport"
            )

    for path, imported in FERMIONIC_SPECIALIZATIONS.items():
        require_owner_import(errors, path, imported)

    # Keep only durable source topology. The removed declaration/body blacklists recorded particular
    # refactor states and helper spellings; they are not reproduced as architecture snapshots.
    finite_trace_import = "LeanCondensedMatter.Transport.FiniteTrace"
    require_owner_import(errors, TRANSPORT / "StredaTraceKernel.lean", finite_trace_import)
    require_owner_import(errors, TRANSPORT / "FiniteDisorder.lean", finite_trace_import)

    resolvent_spectral_import = "LeanCondensedMatter.Transport.ResolventSpectral"
    require_owner_import(errors, TRANSPORT / "FiniteKuboBastin.lean", resolvent_spectral_import)
    require_owner_import(errors, TRANSPORT / "StredaTraceSpectral.lean", resolvent_spectral_import)

    require_owner_import(
        errors,
        FERMIONIC_TRANSPORT / "FrequencyResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching",
    )
    require_owner_import(
        errors,
        FERMIONIC_TRANSPORT / "HarmonicSourceResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.HarmonicSource",
    )
    require_owner_import(
        errors,
        FERMIONIC_TRANSPORT / "StationaryFrequencyResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic",
    )
    require_owner_import(
        errors,
        FERMIONIC_TRANSPORT / "InfiniteTimeFrequencyResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic",
    )

    finite_disorder_resolvent = TRANSPORT / "FiniteDisorderResolvent.lean"
    require_owner_import(
        errors,
        finite_disorder_resolvent,
        "LeanCondensedMatter.Transport.FiniteDisorder",
    )
    require_owner_import(
        errors,
        finite_disorder_resolvent,
        "LeanCondensedMatter.Transport.Resolvent",
    )

    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderMoments.lean",
        "LeanCondensedMatter.Transport.FiniteDisorder",
    )

    finite_disorder_born = TRANSPORT / "FiniteDisorderBorn.lean"
    require_owner_import(
        errors,
        finite_disorder_born,
        "LeanCondensedMatter.Transport.FiniteDisorderMoments",
    )
    require_owner_import(
        errors,
        finite_disorder_born,
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )

    finite_disorder_advanced_born = TRANSPORT / "FiniteDisorderAdvancedBorn.lean"
    require_owner_import(
        errors,
        finite_disorder_advanced_born,
        "LeanCondensedMatter.Transport.FiniteDisorderMoments",
    )
    require_owner_import(
        errors,
        finite_disorder_advanced_born,
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )

    scba = TRANSPORT / "FiniteDisorderSCBA.lean"
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.FiniteDisorder")
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.Resolvent")

    return finish_audit(
        errors,
        failure_heading="Transport architecture audit failed:",
        success_message="Transport architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
