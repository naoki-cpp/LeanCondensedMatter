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

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
