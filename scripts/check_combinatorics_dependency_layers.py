from __future__ import annotations

from pathlib import Path

from architecture_audit_common import (
    finish_audit,
    lean_imports,
    module_matches_prefix,
    repository_root,
)

ROOT = repository_root(__file__)
LEAN_ROOT = ROOT / "LeanCondensedMatter"

LOW_LEVEL_ROOTS = (
    "LeanCondensedMatter.Combinatorics.Cumulant.Moment",
    "LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition",
    "LeanCondensedMatter.Permutation.ConnectedDecomposition",
    "LeanCondensedMatter.Permutation.PairingBridge",
)

FORBIDDEN_PROJECT_PREFIXES = (
    "LeanCondensedMatter.Combinatorics.Cumulant.Inversion",
    "LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion",
    "LeanCondensedMatter.Permutation.Cumulant",
    "LeanCondensedMatter.Combinatorics.SetPartition.Mobius",
)

FORBIDDEN_EXTERNAL_PREFIXES = (
    "Mathlib.Data.Complex",
    "Mathlib.LinearAlgebra.Matrix.Determinant",
    "Mathlib.LinearAlgebra.Matrix.Permanent",
)


def module_path(module: str) -> Path | None:
    prefix = "LeanCondensedMatter."
    if not module.startswith(prefix):
        return None
    relative = module[len(prefix) :].replace(".", "/") + ".lean"
    path = LEAN_ROOT / relative
    return path if path.is_file() else None


def imports(module: str) -> tuple[str, ...]:
    path = module_path(module)
    return () if path is None else lean_imports(path)


def is_forbidden(module: str) -> bool:
    prefixes = (*FORBIDDEN_PROJECT_PREFIXES, *FORBIDDEN_EXTERNAL_PREFIXES)
    return any(module_matches_prefix(module, prefix) for prefix in prefixes)


def check_root(root: str) -> list[str]:
    """Keep the transitive low-level reachability guard that is stronger than a direct-import DAG."""
    findings: list[str] = []
    stack: list[tuple[str, tuple[str, ...]]] = [(root, (root,))]
    visited: set[str] = set()

    while stack:
        module, chain = stack.pop()
        if module in visited:
            continue
        visited.add(module)

        for imported in imports(module):
            next_chain = (*chain, imported)
            if is_forbidden(imported):
                findings.append(" -> ".join(next_chain))
                continue
            if module_path(imported) is not None:
                stack.append((imported, next_chain))

    return findings


def main() -> int:
    # Direct Combinatorics -> Permutation imports are owned by the shared scoped DAG. This focused
    # checker retains only the transitive low-level closure restriction.
    findings: list[str] = []
    for root in LOW_LEVEL_ROOTS:
        findings.extend(check_root(root))
    findings = sorted(set(findings))

    return finish_audit(
        findings,
        failure_heading="Combinatorics dependency-layer audit failed:",
        success_message="Combinatorics dependency-layer audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
