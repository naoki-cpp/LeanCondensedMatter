from __future__ import annotations

import re
from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    lean_source,
    require_files,
    require_import,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
TRANSPORT = LEAN / "Transport"
AHE = TRANSPORT / "AnomalousHall"
FERMIONIC_TRANSPORT = LEAN / "SecondQuantization" / "Fermionic" / "Transport"

# Deliberate source-syntax contract: compatibility forwarding files may be absent from the compiled
# public environment, and their defining property is precisely that they contain imports but no Lean
# declarations. This is not used for semantic owner/type inspection.
DECLARATION_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|class|theorem|lemma)\s+",
    re.MULTILINE,
)

GENERIC_CANONICAL = (
    TRANSPORT / "Core" / "FiniteVolume.lean",
    TRANSPORT / "Core" / "ConductivityNormalization.lean",
    TRANSPORT / "Core" / "FiniteConductivityTable.lean",
    TRANSPORT / "Core" / "FiniteTrace.lean",
    TRANSPORT / "Resolvent" / "Basic.lean",
    TRANSPORT / "Resolvent" / "Spectral.lean",
    TRANSPORT / "Resolvent" / "EnergyDerivative.lean",
    TRANSPORT / "Analysis" / "LorentzianKernel.lean",
    TRANSPORT / "KuboBastin" / "Finite.lean",
    TRANSPORT / "KuboBastin" / "OccupationInterpolation.lean",
    TRANSPORT / "KuboBastin" / "Occupation.lean",
    TRANSPORT / "KuboBastin" / "CommonEnergy.lean",
    TRANSPORT / "Streda" / "OperatorKernel.lean",
    TRANSPORT / "Streda" / "TraceKernel.lean",
    TRANSPORT / "Streda" / "Integration.lean",
    TRANSPORT / "Streda" / "GeneralizedStatic.lean",
    TRANSPORT / "Streda" / "TraceSpectral.lean",
    TRANSPORT / "Streda" / "TraceRepresentation.lean",
    TRANSPORT / "Streda" / "SpectralEnergyIntegral.lean",
    TRANSPORT / "Disorder" / "Finite.lean",
    TRANSPORT / "Disorder" / "Resolvent.lean",
    TRANSPORT / "Disorder" / "Moments.lean",
    TRANSPORT / "Disorder" / "Born.lean",
    TRANSPORT / "Disorder" / "AdvancedBorn.lean",
    TRANSPORT / "Disorder" / "SCBA.lean",
)

GENERIC_COMPAT = {
    "FiniteVolume.lean": "LeanCondensedMatter.Transport.Core.FiniteVolume",
    "ConductivityNormalization.lean": "LeanCondensedMatter.Transport.Core.ConductivityNormalization",
    "FiniteConductivityTable.lean": "LeanCondensedMatter.Transport.Core.FiniteConductivityTable",
    "FiniteTrace.lean": "LeanCondensedMatter.Transport.Core.FiniteTrace",
    "Foundations.lean": "LeanCondensedMatter.Transport.Core",
    "ResolventSpectral.lean": "LeanCondensedMatter.Transport.Resolvent.Spectral",
    "ResolventEnergyDerivative.lean": "LeanCondensedMatter.Transport.Resolvent.EnergyDerivative",
    "ResolventAPI.lean": "LeanCondensedMatter.Transport.Resolvent",
    "LorentzianSpectralKernel.lean": "LeanCondensedMatter.Transport.Analysis.LorentzianKernel",
    "FiniteKuboBastin.lean": "LeanCondensedMatter.Transport.KuboBastin.Finite",
    "OccupationInterpolation.lean": "LeanCondensedMatter.Transport.KuboBastin.OccupationInterpolation",
    "KuboBastinOccupation.lean": "LeanCondensedMatter.Transport.KuboBastin.Occupation",
    "KuboBastinCommonEnergy.lean": "LeanCondensedMatter.Transport.KuboBastin.CommonEnergy",
    "StredaOperatorKernel.lean": "LeanCondensedMatter.Transport.Streda.OperatorKernel",
    "StredaTraceKernel.lean": "LeanCondensedMatter.Transport.Streda.TraceKernel",
    "StredaIntegration.lean": "LeanCondensedMatter.Transport.Streda.Integration",
    "GeneralizedStaticStreda.lean": "LeanCondensedMatter.Transport.Streda.GeneralizedStatic",
    "StredaTraceSpectral.lean": "LeanCondensedMatter.Transport.Streda.TraceSpectral",
    "StredaTraceRepresentation.lean": "LeanCondensedMatter.Transport.Streda.TraceRepresentation",
    "StredaSpectralEnergyIntegral.lean": "LeanCondensedMatter.Transport.Streda.SpectralEnergyIntegral",
    "FiniteDisorder.lean": "LeanCondensedMatter.Transport.Disorder.Finite",
    "FiniteDisorderResolvent.lean": "LeanCondensedMatter.Transport.Disorder.Resolvent",
    "FiniteDisorderMoments.lean": "LeanCondensedMatter.Transport.Disorder.Moments",
    "FiniteDisorderBorn.lean": "LeanCondensedMatter.Transport.Disorder.Born",
    "FiniteDisorderAdvancedBorn.lean": "LeanCondensedMatter.Transport.Disorder.AdvancedBorn",
    "FiniteDisorderSCBA.lean": "LeanCondensedMatter.Transport.Disorder.SCBA",
}

# Canonical implementation modules and migrated downstream specializations must no longer consume
# the compatibility layer. Keep this list incremental so each migration slice can land and be
# guarded independently before the forwarding modules are finally removed.
CANONICAL_IMPORT_MIGRATIONS = {
    TRANSPORT / "Core" / "ConductivityNormalization.lean": (
        ("LeanCondensedMatter.Transport.Core.FiniteVolume",),
        ("LeanCondensedMatter.Transport.FiniteVolume",),
    ),
    TRANSPORT / "Core" / "FiniteConductivityTable.lean": (
        ("LeanCondensedMatter.Transport.Core.ConductivityNormalization",),
        ("LeanCondensedMatter.Transport.ConductivityNormalization",),
    ),
    TRANSPORT / "KuboBastin" / "Finite.lean": (
        ("LeanCondensedMatter.Transport.Resolvent.Spectral",),
        ("LeanCondensedMatter.Transport.ResolventSpectral",),
    ),
    TRANSPORT / "KuboBastin" / "Occupation.lean": (
        (
            "LeanCondensedMatter.Transport.KuboBastin.Finite",
            "LeanCondensedMatter.Transport.KuboBastin.OccupationInterpolation",
        ),
        (
            "LeanCondensedMatter.Transport.FiniteKuboBastin",
            "LeanCondensedMatter.Transport.OccupationInterpolation",
        ),
    ),
    TRANSPORT / "KuboBastin" / "CommonEnergy.lean": (
        ("LeanCondensedMatter.Transport.KuboBastin.Occupation",),
        ("LeanCondensedMatter.Transport.KuboBastinOccupation",),
    ),
    FERMIONIC_TRANSPORT / "ConductivityNormalization.lean": (
        ("LeanCondensedMatter.Transport.Core.ConductivityNormalization",),
        ("LeanCondensedMatter.Transport.ConductivityNormalization",),
    ),
    FERMIONIC_TRANSPORT / "FiniteConductivityTable.lean": (
        ("LeanCondensedMatter.Transport.Core.FiniteConductivityTable",),
        ("LeanCondensedMatter.Transport.FiniteConductivityTable",),
    ),
    FERMIONIC_TRANSPORT / "KuboBastinSpectral.lean": (
        ("LeanCondensedMatter.Transport.KuboBastin.Finite",),
        ("LeanCondensedMatter.Transport.FiniteKuboBastin",),
    ),
    FERMIONIC_TRANSPORT / "CorrectedCurrentKuboBastin.lean": (
        ("LeanCondensedMatter.Transport.KuboBastin.Finite",),
        ("LeanCondensedMatter.Transport.FiniteKuboBastin",),
    ),
    FERMIONIC_TRANSPORT / "KuboBastinOccupation.lean": (
        ("LeanCondensedMatter.Transport.KuboBastin.Occupation",),
        ("LeanCondensedMatter.Transport.KuboBastinOccupation",),
    ),
    FERMIONIC_TRANSPORT / "KuboBastinCommonEnergy.lean": (
        ("LeanCondensedMatter.Transport.KuboBastin.CommonEnergy",),
        ("LeanCondensedMatter.Transport.KuboBastinCommonEnergy",),
    ),
}

AHE_MODEL = {
    "MassiveDirac.lean": "Model.Basic",
    "MassiveDiracCurrentBridge.lean": "Model.CurrentBridge",
    "MassiveDiracSpectral.lean": "Model.Spectral",
}
AHE_INTRINSIC = {
    "MassiveDiracBerryBridge.lean": "Intrinsic.BerryBridge",
    "MassiveDiracBerrySymmetry.lean": "Intrinsic.BerrySymmetry",
    "MassiveDiracIntrinsic.lean": "Intrinsic.Response",
    "MassiveDiracIntrinsicConductivity.lean": "Intrinsic.Conductivity",
}
AHE_STREDA = {
    "MassiveDiracStreda.lean": "Streda.Response",
    "MassiveDiracStredaIntegral.lean": "Streda.Integral",
    "MassiveDiracCurrentOperatorBridge.lean": "Streda.CurrentOperatorBridge",
    "MassiveDiracStredaSpectral.lean": "Streda.Spectral",
}
BASTIN_NAMES = (
    "Berry", "Bands", "Limit", "Lorentzian", "Occupation", "Tail", "FiniteWindow",
    "FermiSurface", "Spectator", "Interband", "PoleFactor", "PoleWindow", "PoleContinuity",
    "PoleWindowContinuity", "PoleWindowBound", "PoleLocalError", "PoleErrorIntegral",
    "PoleInnerError", "PoleOuterError", "PoleErrorSplit", "PoleErrorBound", "PoleErrorLimit",
    "PoleExtraction", "PoleExtractionLimit", "PairIntegral", "PairBerry", "RadialDomination",
    "RadialLimitInterchange", "RadialSpectatorBound", "RadialResolventBound",
    "RadialSpectatorUniformBound", "RadialPairUniformBound", "RadialDominatedConvergence",
    "RadialEnergyBridge", "ZeroTemperaturePair", "CleanConductivity",
)
AHE_BASTIN = {f"MassiveDiracBastin{name}.lean": f"Bastin.{name}" for name in BASTIN_NAMES}
AHE_COMPAT = AHE_MODEL | AHE_INTRINSIC | AHE_STREDA | AHE_BASTIN

AHE_CANONICAL_IMPORT_MIGRATIONS = {
    AHE / "MassiveDirac" / "Model" / "CurrentBridge.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac",),
    ),
    AHE / "MassiveDirac" / "Model" / "Spectral.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "BerryBridge.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Spectral",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracSpectral",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "BerrySymmetry.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.BerryBridge",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerryBridge",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "Response.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.BerrySymmetry",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerrySymmetry",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "Conductivity.lean": (
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.Response",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsic",),
    ),
}


def no_declarations(errors: list[str], path: Path) -> None:
    if not path.is_file():
        return
    if DECLARATION_RE.search(lean_source(path)):
        errors.append(f"{path.relative_to(ROOT)} is compatibility-only and must not own declarations")


def require_compat(errors: list[str], path: Path, module: str) -> None:
    require_import(errors, path, module, root=ROOT, description="compatibility forwarding module")
    no_declarations(errors, path)


def require_canonical_imports(
    errors: list[str], path: Path, required: tuple[str, ...], forbidden: tuple[str, ...]
) -> None:
    for module in required:
        require_import(errors, path, module, root=ROOT, description="canonical transport hierarchy")
    if not path.is_file():
        return
    imports = lean_imports(path)
    for module in forbidden:
        if module in imports:
            errors.append(
                f"{path.relative_to(ROOT)} must import the canonical hierarchy directly, not `{module}`"
            )


def module_path(suffix: str) -> Path:
    parts = suffix.split(".")
    return AHE / "MassiveDirac" / Path(*parts[:-1]) / f"{parts[-1]}.lean"


def main() -> int:
    errors: list[str] = []
    require_files(errors, GENERIC_CANONICAL, root=ROOT, description="physical transport owner")

    for filename, module in GENERIC_COMPAT.items():
        require_compat(errors, TRANSPORT / filename, module)

    for path, (required, forbidden) in CANONICAL_IMPORT_MIGRATIONS.items():
        require_canonical_imports(errors, path, required, forbidden)

    for path, (required, forbidden) in AHE_CANONICAL_IMPORT_MIGRATIONS.items():
        require_canonical_imports(errors, path, required, forbidden)

    transport_umbrella = LEAN / "Transport.lean"
    for module in (
        "LeanCondensedMatter.Transport.Core",
        "LeanCondensedMatter.Transport.Resolvent",
        "LeanCondensedMatter.Transport.KuboBastin",
        "LeanCondensedMatter.Transport.Streda",
        "LeanCondensedMatter.Transport.Disorder",
    ):
        require_import(errors, transport_umbrella, module, root=ROOT, description="transport public umbrella")

    for path in (
        TRANSPORT / "Resolvent" / "Spectral.lean",
        TRANSPORT / "Resolvent" / "EnergyDerivative.lean",
    ):
        require_import(
            errors,
            path,
            "LeanCondensedMatter.Transport.Resolvent.Basic",
            root=ROOT,
            description="resolvent hierarchy",
        )

    ahe_suffixes = (
        set(AHE_MODEL.values())
        | set(AHE_INTRINSIC.values())
        | set(AHE_STREDA.values())
        | set(AHE_BASTIN.values())
    )
    canonical_ahe = tuple(module_path(suffix) for suffix in sorted(ahe_suffixes))
    require_files(errors, canonical_ahe, root=ROOT, description="massive-Dirac physical owner")

    for filename, suffix in AHE_COMPAT.items():
        module = "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac." + suffix
        require_compat(errors, AHE / filename, module)

    ahe_umbrella = TRANSPORT / "AnomalousHall.lean"
    for module in (
        "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model",
        "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic",
        "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda",
        "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin",
    ):
        require_import(errors, ahe_umbrella, module, root=ROOT, description="AHE public umbrella")

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
