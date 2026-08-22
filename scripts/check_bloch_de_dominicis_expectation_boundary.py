from __future__ import annotations

from architecture_audit_common import finish_audit, require_files, require_import, repository_root

ROOT = repository_root(__file__)
TARGET = (
    ROOT
    / "LeanCondensedMatter"
    / "SecondQuantization"
    / "Common"
    / "Thermal"
    / "BlochDeDominicis"
    / "ExpectationRecursion.lean"
)

REQUIRED_IMPORTS = (
    "LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight",
    "LeanCondensedMatter.Combinatorics.PerfectPairing.FirstPairRecursion",
)


def main() -> int:
    errors: list[str] = []

    require_files(errors, (TARGET,), root=ROOT, description="generic expectation recursion module")
    if errors:
        return finish_audit(
            errors,
            failure_heading="Bloch-de Dominicis expectation boundary check failed:",
            success_message="Bloch-de Dominicis expectation boundary check passed",
        )

    for imported in REQUIRED_IMPORTS:
        require_import(
            errors,
            TARGET,
            imported,
            root=ROOT,
            description="generic expectation recursion module",
        )

    # Genericity with respect to finite/density realizations is checked from compiled declaration types.
    return finish_audit(
        errors,
        failure_heading="Bloch-de Dominicis expectation boundary check failed:",
        success_message="Bloch-de Dominicis expectation boundary check passed",
    )


if __name__ == "__main__":
    raise SystemExit(main())
