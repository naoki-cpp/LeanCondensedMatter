from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, require_files

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
LATTICE = FERMIONIC / "Lattice"

REQUIRED = (
    FERMIONIC / "Lattice.lean",
    LATTICE / "DiscreteLattice.lean",
    LATTICE / "Peierls.lean",
    LATTICE / "Bounded.lean",
    LATTICE / "BoundedMatrixUnitAdjoint.lean",
    LATTICE / "PeierlsContact.lean",
    LATTICE / "HermitianBondCurrent.lean",
    LATTICE / "RankOneSecondQuantization.lean",
    LATTICE / "GeometricCurrent.lean",
    LATTICE / "GeometricPeierls.lean",
)


def main() -> int:
    errors: list[str] = []
    # Namespace ownership and response/Transport type separation are compiled contracts.
    require_files(errors, REQUIRED, root=ROOT, description="fermionic lattice owner")
    return finish_audit(
        errors,
        failure_heading="Fermionic lattice boundary audit failed:",
        success_message="Fermionic lattice boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
