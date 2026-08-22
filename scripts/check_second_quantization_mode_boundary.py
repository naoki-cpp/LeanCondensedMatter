from __future__ import annotations

from architecture_audit_common import finish_audit, require_files, repository_root

ROOT = repository_root(__file__)
SQ = ROOT / "LeanCondensedMatter" / "SecondQuantization"

DIMENSION_INDEPENDENT_MODE_FILES = (
    SQ / "Common" / "Algebra" / "OneParticleSpace.lean",
    SQ / "Common" / "Algebra" / "OccupationBasis.lean",
    SQ / "Common" / "Algebra" / "AlgebraicFock.lean",
    SQ / "Fermionic" / "Algebra" / "Occupation.lean",
    SQ / "Fermionic" / "Algebra" / "FockSpace.lean",
    SQ / "Bosonic" / "Algebra" / "Occupation.lean",
    SQ / "Bosonic" / "Algebra" / "FockSpace.lean",
)


def main() -> int:
    errors: list[str] = []
    # Fintype/Finite/DecidableEq restrictions are compiled declaration-type contracts.
    require_files(
        errors,
        DIMENSION_INDEPENDENT_MODE_FILES,
        root=ROOT,
        description="dimension-independent mode module",
    )
    return finish_audit(
        errors,
        failure_heading="SecondQuantization mode-boundary audit failed:",
        success_message="SecondQuantization mode-boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
