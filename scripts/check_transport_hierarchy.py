from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    lean_source,
    require_import,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
TRANSPORT = LEAN / "Transport"
AHE = TRANSPORT / "AnomalousHall"
FERMIONIC_TRANSPORT = LEAN / "SecondQuantization" / "Fermionic" / "Transport"

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

MD = "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac"

AHE_CANONICAL_IMPORT_MIGRATIONS = {
    AHE / "MassiveDirac" / "Model" / "CurrentBridge.lean": (
        (f"{MD}.Model.Basic",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac",),
    ),
    AHE / "MassiveDirac" / "Model" / "Spectral.lean": (
        (f"{MD}.Model.Basic",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "BerryBridge.lean": (
        (f"{MD}.Model.Spectral",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracSpectral",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "BerrySymmetry.lean": (
        (f"{MD}.Intrinsic.BerryBridge",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerryBridge",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "Response.lean": (
        (f"{MD}.Intrinsic.BerrySymmetry",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerrySymmetry",),
    ),
    AHE / "MassiveDirac" / "Intrinsic" / "Conductivity.lean": (
        (f"{MD}.Intrinsic.Response",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsic",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Berry.lean": (
        (
            f"{MD}.Streda.Spectral",
            f"{MD}.Intrinsic.BerryBridge",
            f"{MD}.Streda.CurrentOperatorBridge",
            "LeanCondensedMatter.Transport.Streda.TraceKernel",
        ),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSpectral",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerryBridge",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracCurrentOperatorBridge",
            "LeanCondensedMatter.Transport.StredaTraceKernel",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Bands.lean": (
        (f"{MD}.Bastin.Berry",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBerry",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Limit.lean": (
        (f"{MD}.Bastin.Bands",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBands",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Lorentzian.lean": (
        (f"{MD}.Bastin.Limit", "LeanCondensedMatter.Transport.Analysis.LorentzianKernel"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLimit",
            "LeanCondensedMatter.Transport.LorentzianSpectralKernel",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Occupation.lean": (
        (f"{MD}.Bastin.Lorentzian",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLorentzian",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Tail.lean": (
        (f"{MD}.Bastin.Occupation",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinOccupation",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "FiniteWindow.lean": (
        (f"{MD}.Bastin.Tail",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinTail",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "FermiSurface.lean": (
        (f"{MD}.Bastin.FiniteWindow",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinFiniteWindow",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Spectator.lean": (
        (f"{MD}.Bastin.FermiSurface",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinFermiSurface",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "Interband.lean": (
        (f"{MD}.Bastin.Spectator", f"{MD}.Intrinsic.BerrySymmetry"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinSpectator",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerrySymmetry",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleFactor.lean": (
        (f"{MD}.Bastin.Interband",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinInterband",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleWindow.lean": (
        (f"{MD}.Bastin.PoleFactor",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleFactor",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleContinuity.lean": (
        (f"{MD}.Bastin.PoleWindow",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleWindow",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleWindowContinuity.lean": (
        (f"{MD}.Bastin.PoleContinuity",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleContinuity",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleWindowBound.lean": (
        (f"{MD}.Bastin.PoleWindowContinuity",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleWindowContinuity",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleLocalError.lean": (
        (f"{MD}.Bastin.PoleWindowBound",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleWindowBound",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleErrorIntegral.lean": (
        (f"{MD}.Bastin.PoleLocalError",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleLocalError",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleInnerError.lean": (
        (f"{MD}.Bastin.PoleErrorIntegral",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorIntegral",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleOuterError.lean": (
        (f"{MD}.Bastin.PoleInnerError",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleInnerError",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleErrorSplit.lean": (
        (f"{MD}.Bastin.PoleOuterError",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleOuterError",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleErrorBound.lean": (
        (f"{MD}.Bastin.PoleErrorSplit",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorSplit",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleErrorLimit.lean": (
        (f"{MD}.Bastin.PoleErrorBound",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorBound",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleExtraction.lean": (
        (f"{MD}.Bastin.PoleErrorLimit",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleErrorLimit",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PoleExtractionLimit.lean": (
        (f"{MD}.Bastin.PoleExtraction",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleExtraction",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PairIntegral.lean": (
        (f"{MD}.Bastin.PoleExtractionLimit",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleExtractionLimit",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "PairBerry.lean": (
        (f"{MD}.Bastin.PairIntegral",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPairIntegral",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "CleanConductivity.lean": (
        (f"{MD}.Bastin.PairBerry", f"{MD}.Intrinsic.Conductivity"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPairBerry",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsicConductivity",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialDomination.lean": (
        (f"{MD}.Bastin.PairBerry",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPairBerry",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialLimitInterchange.lean": (
        (f"{MD}.Bastin.CleanConductivity", f"{MD}.Bastin.RadialDomination"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinCleanConductivity",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialDomination",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialSpectatorBound.lean": (
        (f"{MD}.Bastin.RadialDomination",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialDomination",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialResolventBound.lean": (
        (f"{MD}.Bastin.RadialSpectatorBound",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialSpectatorBound",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialSpectatorUniformBound.lean": (
        (f"{MD}.Bastin.RadialResolventBound",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialResolventBound",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialPairUniformBound.lean": (
        (f"{MD}.Bastin.RadialSpectatorUniformBound",),
        ("LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialSpectatorUniformBound",),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialDominatedConvergence.lean": (
        (f"{MD}.Bastin.RadialLimitInterchange", f"{MD}.Bastin.RadialPairUniformBound"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialLimitInterchange",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialPairUniformBound",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "RadialEnergyBridge.lean": (
        (f"{MD}.Bastin.RadialDominatedConvergence", f"{MD}.Bastin.CleanConductivity"),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialDominatedConvergence",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinCleanConductivity",
        ),
    ),
    AHE / "MassiveDirac" / "Bastin" / "ZeroTemperaturePair.lean": (
        (
            f"{MD}.Bastin.RadialEnergyBridge",
            f"{MD}.Bastin.FermiSurface",
            f"{MD}.Bastin.RadialPairUniformBound",
        ),
        (
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialEnergyBridge",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinFermiSurface",
            "LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialPairUniformBound",
        ),
    ),
}


def project_module_path(module: str) -> Path | None:
    prefix = "LeanCondensedMatter."
    if not module.startswith(prefix):
        return None
    return LEAN / (module[len(prefix):].replace(".", "/") + ".lean")


def forwarding_only(errors: list[str], path: Path) -> None:
    """Require a compatibility module to contain imports and the standard header option only."""
    if not path.is_file():
        return

    for line_no, line in enumerate(lean_source(path).splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("import "):
            continue
        if stripped == "set_option linter.style.header false":
            continue
        errors.append(
            f"{path.relative_to(ROOT)}:{line_no} is compatibility-only; "
            f"unexpected Lean command `{stripped}`"
        )


def require_compat(errors: list[str], path: Path, module: str) -> None:
    require_import(errors, path, module, root=ROOT, description="compatibility forwarding module")
    target = project_module_path(module)
    if target is None or not target.is_file():
        errors.append(f"compatibility module target does not exist: `{module}`")
    forwarding_only(errors, path)


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


def main() -> int:
    errors: list[str] = []

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

    for filename, suffix in AHE_COMPAT.items():
        module = f"{MD}.{suffix}"
        require_compat(errors, AHE / filename, module)

    ahe_umbrella = TRANSPORT / "AnomalousHall.lean"
    for module in (
        f"{MD}.Model",
        f"{MD}.Intrinsic",
        f"{MD}.Streda",
        f"{MD}.Bastin",
    ):
        require_import(errors, ahe_umbrella, module, root=ROOT, description="AHE public umbrella")

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())