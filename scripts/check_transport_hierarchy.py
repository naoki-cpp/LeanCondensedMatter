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

MD_IMPL = "LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac"
MD_PUBLIC = "LeanCondensedMatter.Transport.Models.MassiveDirac"
MD_MODEL = f"{MD_PUBLIC}.Model"


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

    models_umbrella = TRANSPORT / "Models.lean"
    require_import(
        errors,
        models_umbrella,
        MD_PUBLIC,
        root=ROOT,
        description="transport models public umbrella",
    )
    massive_dirac_public_umbrella = TRANSPORT / "Models" / "MassiveDirac.lean"
    for module in (
        MD_MODEL,
        f"{MD_PUBLIC}.Propagator",
        f"{MD_IMPL}.Intrinsic",
        f"{MD_PUBLIC}.Streda",
        f"{MD_IMPL}.Bastin",
        f"{MD_PUBLIC}.Disorder",
        f"{MD_PUBLIC}.Conductivity.Longitudinal",
    ):
        require_import(
            errors,
            massive_dirac_public_umbrella,
            module,
            root=ROOT,
            description="massive-Dirac model-owned public entrypoint",
        )

    core_umbrella = TRANSPORT / "Core.lean"
    conductivity_tensor_module = "LeanCondensedMatter.Transport.Core.ConductivityTensor"
    require_import(
        errors,
        core_umbrella,
        conductivity_tensor_module,
        root=ROOT,
        description="transport core public umbrella",
    )
    conductivity_tensor_path = TRANSPORT / "Core" / "ConductivityTensor.lean"
    if any(
        module.startswith("LeanCondensedMatter.Transport.Streda")
        for module in lean_imports(conductivity_tensor_path)
    ):
        errors.append(
            "Transport/Core/ConductivityTensor.lean must remain representation-independent and "
            "must not import Transport.Streda"
        )

    resolvent_umbrella = TRANSPORT / "Resolvent.lean"
    require_import(
        errors,
        resolvent_umbrella,
        "LeanCondensedMatter.Transport.Resolvent.Uniqueness",
        root=ROOT,
        description="resolvent public umbrella",
    )
    lorentzian_kernel_module = "LeanCondensedMatter.Analysis.Lorentzian.Kernel"
    if lorentzian_kernel_module in lean_imports(resolvent_umbrella):
        errors.append(
            "Transport/Resolvent.lean must not re-export Analysis.Lorentzian.Kernel; "
            "Lorentzian analysis is owned by LeanCondensedMatter.Analysis"
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
    if finite_module in lean_imports(pure_point_path):
        errors.append("Transport/KuboBastin/PurePoint.lean must not import Finite")

    streda_umbrella = TRANSPORT / "Streda.lean"
    response_matrix_module = "LeanCondensedMatter.Transport.Streda.ResponseMatrix"
    response_matrix_representation_module = (
        "LeanCondensedMatter.Transport.Streda.ResponseMatrixRepresentation"
    )
    for module in (response_matrix_module, response_matrix_representation_module):
        require_import(
            errors,
            streda_umbrella,
            module,
            root=ROOT,
            description="Streda public umbrella",
        )

    response_matrix_representation_path = TRANSPORT / "Streda" / "ResponseMatrixRepresentation.lean"
    for module in (
        response_matrix_module,
        "LeanCondensedMatter.Transport.Streda.TraceRepresentation",
    ):
        require_import(
            errors,
            response_matrix_representation_path,
            module,
            root=ROOT,
            description="traced Streda response-matrix ownership",
        )

    for path in (
        TRANSPORT / "Streda" / "ResponseMatrix.lean",
        response_matrix_representation_path,
    ):
        if conductivity_tensor_module in lean_imports(path):
            errors.append(
                f"{path.relative_to(ROOT)} must remain at response level and must not import "
                "Transport.Core.ConductivityTensor"
            )

    disorder_umbrella = TRANSPORT / "Disorder.lean"
    averaged_self_energy_module = "LeanCondensedMatter.Transport.Disorder.AveragedSelfEnergy"
    require_import(
        errors,
        disorder_umbrella,
        averaged_self_energy_module,
        root=ROOT,
        description="disorder public umbrella",
    )
    averaged_self_energy_path = TRANSPORT / "Disorder" / "AveragedSelfEnergy.lean"
    for module in (
        "LeanCondensedMatter.Transport.Disorder.Resolvent",
        "LeanCondensedMatter.Transport.Resolvent.SelfEnergy",
    ):
        require_import(
            errors,
            averaged_self_energy_path,
            module,
            root=ROOT,
            description="exact averaged self-energy bridge",
        )

    massive_dirac_model_root = TRANSPORT / "Models" / "MassiveDirac"
    massive_dirac_model_umbrella = massive_dirac_model_root / "Model.lean"
    canonical_operator_module = f"{MD_MODEL}.Operator"
    canonical_operator_spectral_module = f"{MD_MODEL}.OperatorSpectral"
    for module in (canonical_operator_module, canonical_operator_spectral_module):
        require_import(
            errors,
            massive_dirac_model_umbrella,
            module,
            root=ROOT,
            description="massive-Dirac model implementation umbrella",
        )

    massive_dirac_root = TRANSPORT / "AnomalousHall" / "MassiveDirac"
    canonical_propagator_path = massive_dirac_model_root / "Propagator.lean"
    historical_propagator_path = massive_dirac_root / "Propagator.lean"
    require_import(
        errors,
        canonical_propagator_path,
        canonical_operator_spectral_module,
        root=ROOT,
        description="massive-Dirac propagator model ownership",
    )
    if historical_propagator_path.exists():
        errors.append(
            "Transport/AnomalousHall/MassiveDirac/Propagator.lean must not remain after "
            "the propagator owner moves to Transport/Models/MassiveDirac"
        )
    streda_prefix = f"{MD_PUBLIC}.Streda."
    if any(module.startswith(streda_prefix) for module in lean_imports(canonical_propagator_path)):
        errors.append(
            f"{canonical_propagator_path.relative_to(ROOT)} must depend on MassiveDirac.Model, "
            "not MassiveDirac.Streda"
        )

    massive_dirac_streda_umbrella = massive_dirac_model_root / "Streda.lean"
    fiber_response_module = f"{MD_PUBLIC}.Streda.FiberResponse"
    for module in (
        f"{MD_PUBLIC}.Streda.Response",
        f"{MD_PUBLIC}.Streda.Integral",
        fiber_response_module,
    ):
        require_import(
            errors,
            massive_dirac_streda_umbrella,
            module,
            root=ROOT,
            description="massive-Dirac Streda implementation umbrella",
        )
    fiber_response_path = massive_dirac_model_root / "Streda" / "FiberResponse.lean"
    require_import(
        errors,
        fiber_response_path,
        response_matrix_representation_module,
        root=ROOT,
        description="massive-Dirac shared Streda fiber response",
    )

    massive_dirac_bastin_umbrella = massive_dirac_root / "Bastin.lean"
    pole_extraction_module = f"{MD_IMPL}.Bastin.PoleExtraction"
    require_import(
        errors,
        massive_dirac_bastin_umbrella,
        pole_extraction_module,
        root=ROOT,
        description="massive-Dirac Bastin implementation umbrella",
    )
    pair_integral_path = massive_dirac_model_root / "Bastin" / "PairIntegral.lean"
    require_import(
        errors,
        pair_integral_path,
        pole_extraction_module,
        root=ROOT,
        description="massive-Dirac pole extraction consumer",
    )

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
