from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, require_files

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
ALGEBRAIC = FERMIONIC / "Algebra" / "AlgebraicFock"

REQUIRED_FILES = (
    FERMIONIC / "Algebra" / "AlgebraicFock.lean",
    ALGEBRAIC / "Basic.lean",
    ALGEBRAIC / "Creation.lean",
    ALGEBRAIC / "Annihilation.lean",
    ALGEBRAIC / "Mode.lean",
    ALGEBRAIC / "OccupationEquivalence.lean",
    ALGEBRAIC / "OccupationFieldEquivalence.lean",
    ALGEBRAIC / "SecondQuantization.lean",
    ALGEBRAIC / "SecondQuantizationLinearity.lean",
    ALGEBRAIC / "SecondQuantizationCommutator.lean",
    ALGEBRAIC / "RankOne.lean",
)


def main() -> int:
    errors: list[str] = []
    # Namespace ownership and dimension independence are compiled declaration contracts.
    require_files(errors, REQUIRED_FILES, root=ROOT, description="fermionic algebraic-Fock owner")
    return finish_audit(
        errors,
        failure_heading="Fermionic algebraic-Fock boundary audit failed:",
        success_message="Fermionic algebraic-Fock boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
