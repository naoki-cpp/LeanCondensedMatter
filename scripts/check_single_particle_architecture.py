from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root

ROOT = repository_root(__file__)
CONTINUUM = ROOT / "LeanCondensedMatter" / "QuantumMechanics" / "SingleParticle" / "Continuum"


def main() -> int:
    errors: list[str] = []
    # Declaration namespace ownership is checked from compiled metadata.
    if not CONTINUUM.is_dir():
        errors.append(
            "missing canonical single-particle continuum tree: "
            f"{CONTINUUM.relative_to(ROOT)}"
        )
    return finish_audit(
        errors,
        failure_heading="Single-particle architecture audit failed:",
        success_message="Single-particle architecture audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
