from __future__ import annotations

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    module_matches_prefix,
    repository_root,
)

ROOT = repository_root(__file__)
TRANSPORT = ROOT / "LeanCondensedMatter" / "Transport"

MD_PUBLIC = "LeanCondensedMatter.Transport.Models.MassiveDirac"
MD_MODEL = f"{MD_PUBLIC}.Model"


def main() -> int:
    errors: list[str] = []

    # Direct import, umbrella, and simple forbidden-import rules are owned declaratively by
    # scripts/architecture/source_contracts.json. Keep only the one prefix rule that needs an
    # allow-within-forbidden-prefix exception: the canonical propagator may use MassiveDirac.Model
    # but no other MassiveDirac sibling layer.
    canonical_propagator_path = TRANSPORT / "Models" / "MassiveDirac" / "Propagator" / "Basic.lean"
    for module in lean_imports(canonical_propagator_path):
        if module_matches_prefix(module, MD_PUBLIC) and not module_matches_prefix(module, MD_MODEL):
            errors.append(
                f"{canonical_propagator_path.relative_to(ROOT)} must depend only on "
                f"MassiveDirac.Model within the MassiveDirac hierarchy; found `{module}`"
            )

    return finish_audit(
        errors,
        failure_heading="Transport physical-hierarchy audit failed:",
        success_message="Transport physical-hierarchy audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
