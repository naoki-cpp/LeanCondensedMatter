from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    forbid_import_prefixes,
    lean_files,
    lean_imports,
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

SECOND_QUANTIZATION_PREFIX = "LeanCondensedMatter.SecondQuantization"

NEUTRAL_OWNERS = (
    TRANSPORT / "ConductivityNormalization.lean",
    TRANSPORT / "FiniteConductivityTable.lean",
    TRANSPORT / "FiniteKuboBastin.lean",
    TRANSPORT / "StredaOccupation.lean",
    TRANSPORT / "StredaCommonKernel.lean",
    TRANSPORT / "GeneralizedStaticStreda.lean",
    TRANSPORT / "FiniteDisorder.lean",
    TRANSPORT / "FiniteDisorderResolvent.lean",
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


def require_owner_import(errors: list[str], path: Path, imported: str) -> None:
    require_import(errors, path, imported, root=ROOT, description="transport specialization")


def forbid_declarations(
    errors: list[str], path: Path, declarations: tuple[str, ...], owner: str
) -> None:
    if not path.exists():
        return
    text = path.read_text(encoding="utf-8")
    for declaration in declarations:
        if declaration in text:
            errors.append(f"{relative(path)} must not own {owner} declaration `{declaration}`")


def main() -> int:
    errors: list[str] = []

    require_files(errors, NEUTRAL_OWNERS, root=ROOT, description="canonical transport owner")
    require_files(
        errors,
        ADIABATIC_RESPONSE_OWNERS,
        root=ROOT,
        description="canonical linear-response owner",
    )

    for path in lean_files(TRANSPORT):
        forbid_import_prefixes(
            errors,
            path,
            SECOND_QUANTIZATION_PREFIX,
            root=ROOT,
            description="Transport must remain upstream of SecondQuantization",
        )

    for path, imported in FERMIONIC_SPECIALIZATIONS.items():
        require_owner_import(errors, path, imported)

    forbid_declarations(
        errors,
        FERMIONIC_TRANSPORT / "ConductivityNormalization.lean",
        (
            "def adiabaticElectricFieldFactor",
            "def finiteVolumeConductivityNormalization",
            "def finiteVolumeConductivityFromVectorPotential",
        ),
        "generic normalization",
    )
    forbid_declarations(
        errors,
        FERMIONIC_TRANSPORT / "FiniteConductivityTable.lean",
        (
            "structure FiniteConductivityTable",
            "def finiteConductivityTableValue",
        ),
        "generic scalar table",
    )

    frequency_response = FERMIONIC_TRANSPORT / "FrequencyResponse.lean"
    require_owner_import(
        errors,
        frequency_response,
        "LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching",
    )
    if frequency_response.exists():
        frequency_code = frequency_response.read_text(encoding="utf-8")
        if "adiabaticFrequencyPhase" not in frequency_code:
            errors.append(
                f"{relative(frequency_response)} must consume the canonical adiabatic frequency phase"
            )
    forbid_declarations(
        errors,
        frequency_response,
        (
            "def finiteTimeAdiabaticTransform",
            "def HasInfiniteObservationTimeLimit",
            "def HasZeroSwitchingLimit",
            "def HasDCFrequencyLimit",
            "def HasTimeThenSwitchingThenDCLimit",
            "def HasTimeThenDCThenSwitchingLimit",
        ),
        "generic response core",
    )

    fermionic_harmonic = FERMIONIC_TRANSPORT / "HarmonicSourceResponse.lean"
    require_owner_import(
        errors,
        fermionic_harmonic,
        "LeanCondensedMatter.QuantumTheory.LinearResponse.HarmonicSource",
    )
    forbid_declarations(
        errors,
        fermionic_harmonic,
        (
            "def adiabaticCosineSource",
            "def adiabaticSineSource",
            "theorem adiabaticFrequencyFactor_eq_cosine_add_I_sine",
            "theorem adiabaticCosineSource_at_observation",
            "theorem adiabaticSineSource_at_observation",
        ),
        "generic harmonic-source",
    )

    require_owner_import(
        errors,
        FERMIONIC_TRANSPORT / "StationaryFrequencyResponse.lean",
        "LeanCondensedMatter.QuantumTheory.LinearResponse.FiniteTimeAdiabatic",
    )

    fermionic_infinite = FERMIONIC_TRANSPORT / "InfiniteTimeFrequencyResponse.lean"
    require_owner_import(
        errors,
        fermionic_infinite,
        "LeanCondensedMatter.QuantumTheory.LinearResponse.InfiniteTimeAdiabatic",
    )
    forbid_declarations(
        errors,
        fermionic_infinite,
        (
            "def AdiabaticLagIntegrable",
            "def infiniteTimeAdiabaticTransform",
            "theorem hasInfiniteObservationTimeLimit_finiteTimeAdiabaticTransform",
        ),
        "generic infinite-time response",
    )

    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderResolvent.lean",
        "LeanCondensedMatter.Transport.FiniteDisorder",
    )
    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderResolvent.lean",
        "LeanCondensedMatter.Transport.Resolvent",
    )
    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )
    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderBorn",
    )
    require_owner_import(
        errors,
        TRANSPORT / "FiniteDisorderAdvancedBorn.lean",
        "LeanCondensedMatter.Transport.FiniteDisorderResolvent",
    )

    scba = TRANSPORT / "FiniteDisorderSCBA.lean"
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.FiniteDisorder")
    require_owner_import(errors, scba, "LeanCondensedMatter.Transport.Resolvent")
    for forbidden in (
        "LeanCondensedMatter.Transport.FiniteDisorderBorn",
        "LeanCondensedMatter.Transport.FiniteDisorderAdvancedBorn",
    ):
        if scba.exists() and forbidden in lean_imports(scba):
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
