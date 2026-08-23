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

CORE = TRANSPORT / "Core"
RESOLVENT = TRANSPORT / "Resolvent"
KUBO_BASTIN = TRANSPORT / "KuboBastin"
STREDA = TRANSPORT / "Streda"
DISORDER = TRANSPORT / "Disorder"

NEUTRAL_OWNERS = (
    CORE / "ConductivityNormalization.lean",
    CORE / "FiniteConductivityTable.lean",
    CORE / "FiniteTrace.lean",
    RESOLVENT / "Basic.lean",
    RESOLVENT / "Spectral.lean",
    KUBO_BASTIN / "Finite.lean",
    KUBO_BASTIN / "Occupation.lean",
    KUBO_BASTIN / "CommonEnergy.lean",
    STREDA / "GeneralizedStatic.lean",
    DISORDER / "Finite.lean",
    DISORDER / "Resolvent.lean",
    DISORDER / "Moments.lean",
    DISORDER / "Born.lean",
    DISORDER / "AdvancedBorn.lean",
    DISORDER / "SCBA.lean",
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
        "LeanCondensedMatter.Transport.Streda.GeneralizedStatic",
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
    finite_trace_import = "LeanCondensedMatter.Transport.Core.FiniteTrace"
    streda_trace_kernel = STREDA / "TraceKernel.lean"
    require_owner_import(errors, streda_trace_kernel, finite_trace_import)
    require_owner_import(
        errors,
        streda_trace_kernel,
        "LeanCondensedMatter.Transport.Streda.OperatorKernel",
    )

    require_owner_import(errors, DISORDER / "Finite.lean", finite_trace_import)

    resolvent_spectral_import = "LeanCondensedMatter.Transport.Resolvent.Spectral"
    require_owner_import(errors, KUBO_BASTIN / "Finite.lean", resolvent_spectral_import)
    require_owner_import(errors, STREDA / "TraceSpectral.lean", resolvent_spectral_import)

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

    finite_disorder_resolvent = DISORDER / "Resolvent.lean"
    require_owner_import(
        errors,
        finite_disorder_resolvent,
        "LeanCondensedMatter.Transport.Disorder.Finite",
    )
    require_owner_import(
        errors,
        finite_disorder_resolvent,
        "LeanCondensedMatter.Transport.Resolvent.Basic",
    )

    require_owner_import(
        errors,
        DISORDER / "Moments.lean",
        "LeanCondensedMatter.Transport.Disorder.Finite",
    )

    finite_disorder_born = DISORDER / "Born.lean"
    require_owner_import(
        errors,
        finite_disorder_born,
        "LeanCondensedMatter.Transport.Disorder.Moments",
    )
    require_owner_import(
        errors,
        finite_disorder_born,
        "LeanCondensedMatter.Transport.Disorder.Resolvent",
    )

    finite_disorder_advanced_born = DISORDER / "AdvancedBorn.lean"
    require_owner_import(
        errors,
        finite_disorder_advanced_born,
        "LeanCondensedMatter.Transport.Disorder.Moments",
    )
    require_owner_import(
        errors,
        finite_disorder_advanced_born,
        "LeanCondensedMatter.Transport.Disorder.Resolvent",
    )

    scba = DISORDER / "SCBA.lean"
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.Disorder.Finite")
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.Resolvent.Basic")

    return finish_audit(
        errors,
        failure_heading="Transport architecture audit failed:",
        success_message="Transport architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
