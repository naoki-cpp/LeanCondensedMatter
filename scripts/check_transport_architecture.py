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
FERMIONIC_TRANSPORT = LEAN / "SecondQuantization" / "Fermionic" / "Transport"

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)")
SECOND_QUANTIZATION_PREFIX = "LeanCondensedMatter.SecondQuantization"

NEUTRAL_OWNERS = (
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

REMOVED_GENERIC_FERMIONIC_OWNERS = (
    FERMIONIC_TRANSPORT / "GeneralizedKuboBastin.lean",
    FERMIONIC_TRANSPORT / "StredaCommonEnergyBridge.lean",
    FERMIONIC_TRANSPORT / "GeneralizedStaticStreda.lean",
)

FERMIONIC_SPECIALIZATIONS = {
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
    # Kubo–Bastin/Středa authority stays in Transport.
    for path, imported in FERMIONIC_SPECIALIZATIONS.items():
        require_import(errors, path, imported)

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
