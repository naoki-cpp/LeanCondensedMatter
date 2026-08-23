from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_files,
    lean_imports,
    lean_source,
    numbered_imports,
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


def project_module_path(module: str) -> Path | None:
    prefix = "LeanCondensedMatter."
    if not module.startswith(prefix):
        return None
    return LEAN / (module[len(prefix):].replace(".", "/") + ".lean")


def forwarding_only(errors: list[str], path: Path) -> None:
    """Require a compatibility module to contain imports and the standard header option only."""
    if not path.is_file():
        return

    import_lines = {line_no for line_no, _ in numbered_imports(path)}
    for line_no, line in enumerate(lean_source(path).splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if line_no in import_lines:
            continue
        if stripped == "set_option linter.style.header false":
            continue
        errors.append(
            f"{path.relative_to(ROOT)}:{line_no} is compatibility-only; "
            f"unexpected Lean command `{stripped}`"
        )


def require_compat(errors: list[str], path: Path, module: str) -> None:
    """Require a declaration-free forwarding module with exactly one canonical import."""
    if not path.is_file():
        errors.append(f"missing compatibility forwarding module: {path.relative_to(ROOT)}")
        return

    imports = lean_imports(path)
    if imports != (module,):
        rendered = ", ".join(f"`{imported}`" for imported in imports) or "<none>"
        errors.append(
            f"{path.relative_to(ROOT)} must import exactly `{module}`, found {rendered}"
        )

    target = project_module_path(module)
    if target is None or not target.is_file():
        errors.append(f"compatibility module target does not exist: `{module}`")
    forwarding_only(errors, path)


def flat_module_names(prefix: str, compatibility: dict[str, str]) -> frozenset[str]:
    """Derive historical flat module names from their forwarding filenames."""
    return frozenset(f"{prefix}.{Path(filename).stem}" for filename in compatibility)


def forbid_compat_imports_under(
    errors: list[str],
    source_root: Path,
    forbidden_modules: frozenset[str],
    *,
    description: str,
) -> None:
    """Prevent every canonical consumer under a tree from regressing to a compatibility shim."""
    if not source_root.is_dir():
        errors.append(f"missing {description}: {source_root.relative_to(ROOT)}")
        return
    for path in lean_files(source_root):
        for line_no, imported in numbered_imports(path):
            if imported in forbidden_modules:
                errors.append(
                    f"{path.relative_to(ROOT)}:{line_no} must import the canonical hierarchy "
                    f"directly, not compatibility module `{imported}`"
                )


def main() -> int:
    errors: list[str] = []

    for filename, module in GENERIC_COMPAT.items():
        require_compat(errors, TRANSPORT / filename, module)

    # The compatibility map is the single source of truth for both forwarding targets and forbidden
    # historical imports. This replaces the per-file migration table: every current and future
    # canonical module is guarded automatically.
    generic_flat_modules = flat_module_names("LeanCondensedMatter.Transport", GENERIC_COMPAT)
    for directory in ("Core", "Resolvent", "Analysis", "KuboBastin", "Streda", "Disorder"):
        forbid_compat_imports_under(
            errors,
            TRANSPORT / directory,
            generic_flat_modules,
            description=f"canonical Transport/{directory} hierarchy",
        )
    forbid_compat_imports_under(
        errors,
        FERMIONIC_TRANSPORT,
        generic_flat_modules,
        description="fermionic transport specialization hierarchy",
    )

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

    ahe_flat_modules = flat_module_names(
        "LeanCondensedMatter.Transport.AnomalousHall", AHE_COMPAT
    )
    forbid_compat_imports_under(
        errors,
        AHE / "MassiveDirac",
        ahe_flat_modules,
        description="canonical massive-Dirac AHE hierarchy",
    )

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
