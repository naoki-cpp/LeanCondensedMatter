from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    check_absent_paths,
    finish_audit,
    lean_files,
    numbered_lines,
    relative as relative_to,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
TRANSPORT = LEAN / "Transport"
LINEAR_RESPONSE = LEAN / "QuantumTheory" / "LinearResponse"
FERMIONIC_TRANSPORT = LEAN / "SecondQuantization" / "Fermionic" / "Transport"

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)")
SECOND_QUANTIZATION_PREFIX = "LeanCondensedMatter.SecondQuantization"

NEUTRAL_OWNERS = (
    TRANSPORT / "ConductivityNormalization.lean",
    TRANSPORT / "FiniteConductivityTable.lean",
    TRANSPORT / "FiniteKuboBastin.lean",
    TRANSPORT / "StredaOccupation.lean",
    TRANSPORT / "StredaCommonKernel.lean",
    TRANSPORT / "StredaCommonEnergyBridge.lean",
    TRANSPORT / "GeneralizedStaticStreda.lean",
    TRANSPORT / "FiniteDisorder.lean",
    TRANSPORT / "FiniteDisorderResolvent.lean",
    TRANSPORT / "FiniteDisorderBorn.lean",
    TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
    TRANSPORT / "FiniteDisorderSCBA.lean",
)

ADIABATIC_RESPONSE_OWNERS = (
    LINEAR_RESPONSE / "HarmonicSource.lean",
    LINEAR_RESPONSE / "FiniteTimeAdiabatic.lean",
    LINEAR_RESPONSE / "InfiniteTimeAdiabatic.lean",
)

REMOVED_GENERIC_FERMIONIC_OWNERS = (
    FERMIONIC_TRANSPORT / "GeneralizedKuboBastin.lean",
    FERMIONIC_TRANSPORT / "StredaCommonEnergyBridge.lean",
    FERMIONIC_TRANSPORT / "GeneralizedStaticStreda.lean",
)

FERMIONIC_SPECIALIZATIONS = {
    FERMIONIC_TRANSPORT / "ConductivityNormalization.lean":
        "LeanCondensedMatter.Transport.ConductivityNormalization",
    FERMIONIC_TRANSPORT / "FiniteConductivityTable.lean":
        "LeanCondensedMatter.Transport.FiniteConductivityTable",
    FERMIONIC_TRANSPORT / "KuboBastinSpectral.lean":
        "LeanCondensedMatter.Transport.FiniteKuboBastin",
    FERMIONIC_TRANSPORT / "StredaOccupation.lean":
        "LeanCondensedMatter.Transport.StredaOccupation",
    FERMIONIC_TRANSPORT / "StredaCommonKernel.lean":
        "LeanCondensedMatter.Transport.StredaCommonKernel",
    FERMIONIC_TRANSPORT / "StaticKuboBastinResponse.lean":
        "LeanCondensedMatter.Transport.GeneralizedStaticStreda",
}


def relative(path: Path) -> str:
    return relative_to(ROOT, path)


def imports(path: Path) -> tuple[str, ...]:
    found: list[str] = []
    for _, line in numbered_lines(path):
        if match := IMPORT_RE.match(line):
            found.append(match.group(1))
    return tuple(found)


def require_exists(errors: list[str], path: Path) -> None:
    if not path.exists():
        errors.append(f"missing canonical transport owner: {relative(path)}")


def require_import(errors: list[str], path: Path, imported: str) -> None:
    if not path.exists():
        errors.append(f"missing transport specialization: {relative(path)}")
        return
    if imported not in imports(path):
        errors.append(f"{relative(path)} must import canonical owner `{imported}`")


def forbid_import_prefix(
    errors: list[str], path: Path, prefix: str, description: str
) -> None:
    for imported in imports(path):
        if imported.startswith(prefix):
            errors.append(
                f"{description}: {relative(path)} imports forbidden downstream module `{imported}`"
            )


def main() -> int:
    errors: list[str] = []

    for path in NEUTRAL_OWNERS:
        require_exists(errors, path)

    for path in ADIABATIC_RESPONSE_OWNERS:
        if not path.exists():
            errors.append(f"missing canonical linear-response owner: {relative(path)}")

    check_absent_paths(
        errors,
        REMOVED_GENERIC_FERMIONIC_OWNERS,
        root=ROOT,
        description="retired generic fermionic transport owner must stay removed",
    )

    # Generic transport, including concrete model consumers under Transport/AnomalousHall,
    # must never acquire a dependency on particle-statistics realizations.
    for path in lean_files(TRANSPORT):
        forbid_import_prefix(
            errors,
            path,
            SECOND_QUANTIZATION_PREFIX,
            "Transport must remain upstream of SecondQuantization",
        )

    # Fermionic directional/current modules may specialize neutral transport, but the generic
    # Kubo–Bastin/Středa/normalization/scalar-evaluation authority stays in Transport.
    for path, imported in FERMIONIC_SPECIALIZATIONS.items():
        require_import(errors, path, imported)

    # The fermionic conductivity-normalization module is only a directional realization. The
    # scalar vector-potential/electric-field conversion must not be redefined downstream.
    fermionic_normalization = FERMIONIC_TRANSPORT / "ConductivityNormalization.lean"
    if fermionic_normalization.exists():
        text = fermionic_normalization.read_text(encoding="utf-8")
        for declaration in (
            "def adiabaticElectricFieldFactor",
            "def finiteVolumeConductivityNormalization",
            "def finiteVolumeConductivityFromVectorPotential",
        ):
            if declaration in text:
                errors.append(
                    f"{relative(fermionic_normalization)} must not re-own generic normalization `{declaration}`"
                )

    # The fermionic conductivity-table module constructs the directional Peierls realization only.
    # Generic scalar table storage/evaluation belongs to Transport.
    fermionic_table = FERMIONIC_TRANSPORT / "FiniteConductivityTable.lean"
    if fermionic_table.exists():
        text = fermionic_table.read_text(encoding="utf-8")
        for declaration in (
            "structure FiniteConductivityTable",
            "def finiteConductivityTableValue",
        ):
            if declaration in text:
                errors.append(
                    f"{relative(fermionic_table)} must not re-own generic scalar table `{declaration}`"
                )

    # Scalar finite-time adiabatic transformation and observation-time convergence are generic
    # linear-response concepts. Fermionic transport must not reintroduce its retired copies.
    fermionic_frequency = FERMIONIC_TRANSPORT / "FrequencyResponse.lean"
    if fermionic_frequency.exists():
        text = fermionic_frequency.read_text(encoding="utf-8")
        for declaration in (
            "def finiteTimeAdiabaticTransform",
            "def HasInfiniteObservationTimeLimit",
            "def HasZeroSwitchingLimit",
            "def HasDCFrequencyLimit",
            "def HasTimeThenSwitchingThenDCLimit",
            "def HasTimeThenDCThenSwitchingLimit",
        ):
            if declaration in text:
                errors.append(
                    f"{relative(fermionic_frequency)} must not re-own generic response core `{declaration}`"
                )

    # Real harmonic source quadratures are scalar linear-response data rather than a fermionic
    # transport construction. The directional response module must consume the canonical owner.
    fermionic_harmonic = FERMIONIC_TRANSPORT / "HarmonicSourceResponse.lean"
    require_import(
        errors,
        fermionic_harmonic,
        "LeanCondensedMatter.QuantumTheory.LinearResponse.HarmonicSource",
    )
    if fermionic_harmonic.exists():
        text = fermionic_harmonic.read_text(encoding="utf-8")
        for declaration in (
            "def adiabaticCosineSource",
            "def adiabaticSineSource",
            "theorem adiabaticFrequencyFactor_eq_cosine_add_I_sine",
            "theorem adiabaticCosineSource_at_observation",
            "theorem adiabaticSineSource_at_observation",
        ):
            if declaration in text:
                errors.append(
                    f"{relative(fermionic_harmonic)} must not re-own generic harmonic source `{declaration}`"
                )

    require_import(
        errors,
        FERMIONIC_TRANSPORT / "StationaryFrequencyResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic",
    )

    # Scalar positive-lag integrability, the half-infinite transform, and the finite-time to
    # infinite-time convergence theorem are likewise generic linear-response concepts.
    fermionic_infinite = FERMIONIC_TRANSPORT / "InfiniteTimeFrequencyResponse.lean"
    require_import(
        errors,
        fermionic_infinite,
        "LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic",
    )
    if fermionic_infinite.exists():
        text = fermionic_infinite.read_text(encoding="utf-8")
        for declaration in (
            "def AdiabaticLagIntegrable",
            "def infiniteTimeAdiabaticTransform",
            "theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform",
        ):
            if declaration in text:
                errors.append(
                    f"{relative(fermionic_infinite)} must not re-own generic infinite-time response `{declaration}`"
                )

    # Exact finite disorder owns the ensemble and exact averages. Configuration-wise resolvent
    # identities are a separate exact layer consumed by first Born and advanced Born.
    require_import(
        errors,
        TRANSPORT / "FiniteDisorderResolvent.lean",
        "LeanCondensedMatter.Transport.FiniteDisorder",
    )
    require_import(
        errors,
        TRANSPORT / "FiniteDisorderResolvent.lean",
        "LeanCondensedMatter.Transport.Resolvent",
    )
    require_import(
        errors,
        TRANSPORT / "FiniteDisorderBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )
    require_import(
        errors,
        TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderBorn",
    )
    require_import(
        errors,
        TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )

    # SCBA is a sibling approximation layer over the exact finite ensemble and generic resolvent
    # algebra; it must not depend on the first-Born closure layer.
    scba = TRANSPORT / "FiniteDisorderSCBA.lean"
    require_import(errors, scba, "LeanCondensedMatter.Transport.FiniteDisorder")
    require_import(errors, scba, "LeanCondensedMatter.Transport.Resolvent")
    for forbidden in (
        "LeanCondensedMatter.Transport.FiniteDisorderBorn",
        "LeanCondensedMatter.Transport.FiniteDisorderAdvancedBorn",
    ):
        if scba.exists() and forbidden in imports(scba):
            errors.append(
                f"{relative(scba)} must remain independent of Born closure owner `{forbidden}`"
            )

    return finish_audit(
        errors,
        failure_heading="Transport architecture audit failed:",
        success_message="Transport architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
