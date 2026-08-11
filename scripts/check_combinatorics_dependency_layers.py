from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "LeanCondensedMatter"

IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$")

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


def imports(module: str) -> list[str]:
    path = module_path(module)
    if path is None:
        return []
    result: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            result.append(match.group(1))
    return result


def is_forbidden(module: str) -> bool:
    return module.startswith(FORBIDDEN_PROJECT_PREFIXES + FORBIDDEN_EXTERNAL_PREFIXES)


def check_root(root: str) -> list[str]:
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


def main() -> None:
    findings: list[str] = []
    for root in LOW_LEVEL_ROOTS:
        findings.extend(check_root(root))

    if findings:
        print("Combinatorics dependency-layer audit failed:")
        for finding in sorted(set(findings)):
            print(f"- {finding}")
        raise SystemExit(1)

    print("Combinatorics dependency-layer audit passed.")


if __name__ == "__main__":
    main()
