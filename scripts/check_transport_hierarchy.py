from __future__ import annotations

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    require_import,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN = ROOT / "LeanCondensedMatter"
TRANSPORT = LEAN / "Transport"

MD = "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac"


def main() -> int:
    errors: list[str] = []

    transport_umbrella = LEAN / "Transport.lean"
    for module in (
        "LeanCondensedMatter.Transport.Core",
        "LeanCondensedMatter.Transport.Resolvent",
        "LeanCondensedMatter.Transport.KuboBastin",
        "LeanCondensedMatter.Transport.Streda",
        "LeanCondensedMatter.Transport.Disorder",
    ):
        require_import(errors, transport_umbrella, module, root=ROOT, description="transport public umbrella")

    resolvent_umbrella = TRANSPORT / "Resolvent.lean"
    for module in (
        "LeanCondensedMatter.Transport.Resolvent.DressedEnergyDerivative",
        "LeanCondensedMatter.Transport.Resolvent.Uniqueness",
    ):
        require_import(
            errors,
            resolvent_umbrella,
            module,
            root=ROOT,
            description="resolvent public umbrella",
        )
    for path in (
        TRANSPORT / "Resolvent" / "Spectral.lean",
        TRANSPORT / "Resolvent" / "EnergyDerivative.lean",
        TRANSPORT / "Resolvent" / "Uniqueness.lean",
    ):
        require_import(
            errors,
            path,
            "LeanCondensedMatter.Transport.Resolvent.Basic",
            root=ROOT,
            description="resolvent hierarchy",
        )
    require_import(
        errors,
        TRANSPORT / "Resolvent" / "DressedEnergyDerivative.lean",
        "LeanCondensedMatter.Transport.Resolvent.EnergyDerivative",
        root=ROOT,
        description="dressed resolvent energy calculus",
    )

    kubo_bastin_umbrella = TRANSPORT / "KuboBastin.lean"
    pure_point_module = "LeanCondensedMatter.Transport.KuboBastin.PurePoint"
    finite_module = "LeanCondensedMatter.Transport.KuboBastin.Finite"
    for module in (pure_point_module, finite_module):
        require_import(
            errors,
            kubo_bastin_umbrella,
            module,
            root=ROOT,
            description="Kubo-Bastin public umbrella",
        )

    pure_point_path = TRANSPORT / "KuboBastin" / "PurePoint.lean"
    finite_path = TRANSPORT / "KuboBastin" / "Finite.lean"
    require_import(
        errors,
        finite_path,
        pure_point_module,
        root=ROOT,
        description="finite Kubo-Bastin specialization",
    )
    if finite_module in lean_imports(pure_point_path):
        errors.append("Transport/KuboBastin/PurePoint.lean must not import Finite")

    retired_finite_trace_path = TRANSPORT / "KuboBastin" / "FiniteTrace.lean"
    if retired_finite_trace_path.exists():
        errors.append(
            "Transport/KuboBastin/FiniteTrace.lean is retired; "
            "ordinary operator traces belong under Transport/Streda"
        )

    disorder_umbrella = TRANSPORT / "Disorder.lean"
    born_common_module = "LeanCondensedMatter.Transport.Disorder.BornCommon"
    require_import(
        errors,
        disorder_umbrella,
        born_common_module,
        root=ROOT,
        description="disorder public umbrella",
    )
    retarded_born_path = TRANSPORT / "Disorder" / "RetardedBorn.lean"
    advanced_born_path = TRANSPORT / "Disorder" / "AdvancedBorn.lean"
    for path in (retarded_born_path, advanced_born_path):
        require_import(
            errors,
            path,
            born_common_module,
            root=ROOT,
            description="Born specialization",
        )

    retired_born_path = TRANSPORT / "Disorder" / "Born.lean"
    if retired_born_path.exists():
        errors.append("Transport/Disorder/Born.lean is retired; use RetardedBorn.lean")

    retarded_born_module = "LeanCondensedMatter.Transport.Disorder.RetardedBorn"
    advanced_born_module = "LeanCondensedMatter.Transport.Disorder.AdvancedBorn"
    if advanced_born_module in lean_imports(retarded_born_path):
        errors.append("Transport/Disorder/RetardedBorn.lean must not import AdvancedBorn")
    if retarded_born_module in lean_imports(advanced_born_path):
        errors.append("Transport/Disorder/AdvancedBorn.lean must not import RetardedBorn")

    ahe_umbrella = TRANSPORT / "AnomalousHall.lean"
    for module in (
        f"{MD}.Model",
        f"{MD}.Intrinsic",
        f"{MD}.Streda",
        f"{MD}.Bastin",
    ):
        require_import(errors, ahe_umbrella, module, root=ROOT, description="AHE public umbrella")

    massive_dirac_root = TRANSPORT / "AnomalousHall" / "MassiveDirac"
    massive_dirac_model_umbrella = massive_dirac_root / "Model.lean"
    operator_module = f"{MD}.Model.Operator"
    operator_spectral_module = f"{MD}.Model.OperatorSpectral"
    for module in (operator_module, operator_spectral_module):
        require_import(
            errors,
            massive_dirac_model_umbrella,
            module,
            root=ROOT,
            description="massive-Dirac model public umbrella",
        )

    propagator_path = massive_dirac_root / "Propagator.lean"
    scalar_disorder_path = massive_dirac_root / "Disorder" / "ScalarCovariance.lean"
    require_import(
        errors,
        propagator_path,
        operator_spectral_module,
        root=ROOT,
        description="massive-Dirac propagator model ownership",
    )
    require_import(
        errors,
        scalar_disorder_path,
        operator_module,
        root=ROOT,
        description="massive-Dirac disorder model ownership",
    )
    streda_prefix = f"{MD}.Streda."
    for path in (propagator_path, scalar_disorder_path):
        if any(module.startswith(streda_prefix) for module in lean_imports(path)):
            errors.append(
                f"{path.relative_to(ROOT)} must depend on MassiveDirac.Model, not MassiveDirac.Streda"
            )

    massive_dirac_streda_umbrella = massive_dirac_root / "Streda.lean"
    for module in (f"{MD}.Streda.Response", f"{MD}.Streda.Integral"):
        require_import(
            errors,
            massive_dirac_streda_umbrella,
            module,
            root=ROOT,
            description="massive-Dirac Streda public umbrella",
        )
    for retired_path in (
        massive_dirac_root / "Streda" / "CurrentOperatorBridge.lean",
        massive_dirac_root / "Streda" / "Spectral.lean",
    ):
        if retired_path.exists():
            errors.append(
                f"{retired_path.relative_to(ROOT)} is retired; "
                "bounded current/spectral infrastructure belongs under MassiveDirac/Model"
            )

    massive_dirac_bastin_umbrella = TRANSPORT / "AnomalousHall" / "MassiveDirac" / "Bastin.lean"
    pole_extraction_module = f"{MD}.Bastin.PoleExtraction"
    require_import(
        errors,
        massive_dirac_bastin_umbrella,
        pole_extraction_module,
        root=ROOT,
        description="massive-Dirac Bastin public umbrella",
    )
    pair_integral_path = (
        TRANSPORT / "AnomalousHall" / "MassiveDirac" / "Bastin" / "PairIntegral.lean"
    )
    require_import(
        errors,
        pair_integral_path,
        pole_extraction_module,
        root=ROOT,
        description="massive-Dirac pole extraction consumer",
    )
    retired_pole_extraction_limit_path = (
        TRANSPORT / "AnomalousHall" / "MassiveDirac" / "Bastin" / "PoleExtractionLimit.lean"
    )
    if retired_pole_extraction_limit_path.exists():
        errors.append(
            "MassiveDirac/Bastin/PoleExtractionLimit.lean is retired; "
            "keep the limit theorem in PoleExtraction.lean"
        )

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
