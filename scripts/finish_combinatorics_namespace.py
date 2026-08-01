from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "LeanCondensedMatter"

IMPORT_REPLACEMENTS = {
    "LeanCondensedMatter.Combinatorics.IncidenceAlgebraMu":
        "LeanCondensedMatter.Combinatorics.IncidenceAlgebra.Mobius",
    "LeanCondensedMatter.Combinatorics.PartitionLattice":
        "LeanCondensedMatter.Combinatorics.SetPartition.Mobius",
    "LeanCondensedMatter.Combinatorics.MomentCumulant":
        "LeanCondensedMatter.Combinatorics.Cumulant.Inversion",
    "LeanCondensedMatter.Combinatorics.CumulantFactorization":
        "LeanCondensedMatter.Combinatorics.Cumulant.Independence",
    "LeanCondensedMatter.Combinatorics.DiagramConnectedness":
        "LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition",
    "LeanCondensedMatter.Combinatorics.Common.DeletedFinPositionsSuccAbove":
        "LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositionsSuccAbove",
    "LeanCondensedMatter.Combinatorics.Common.DeletedFinPositions":
        "LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions",
    "LeanCondensedMatter.Combinatorics.Common.EraseIdxOfFn":
        "LeanCondensedMatter.Combinatorics.FiniteIndex.EraseIdxOfFn",
    "LeanCondensedMatter.Combinatorics.PowerSeriesCumulant":
        "LeanCondensedMatter.Analysis.PowerSeries.Cumulant",
    "LeanCondensedMatter.Combinatorics.BinaryShuffleIntegrand":
        "LeanCondensedMatter.Analysis.OrderedSimplex.BinaryShuffleIntegrand",
}

QUALIFIED_REPLACEMENTS = {
    "SecondQuantization.Common.BlochDeDominicis.Pairing": "Combinatorics.Pairing",
    "SecondQuantization.Common.BlochDeDominicis.IsPairing": "Combinatorics.IsPairing",
    "SecondQuantization.Common.BlochDeDominicis.Crosses": "Combinatorics.Crosses",
    "SecondQuantization.Common.BlochDeDominicis.allPairings": "Combinatorics.allPairings",
    "SecondQuantization.Common.BlochDeDominicis.mem_allPairings": "Combinatorics.mem_allPairings",
}

PAIRING_TOKEN = re.compile(
    r"\b(?:Pairing|IsPairing|Crosses|allPairings|mem_allPairings|pairingAdjacent|pairingCrossing|pairingNested)\b"
)


def insert_open_combinatorics(text: str) -> str:
    if re.search(r"(?m)^open(?: scoped)? .*\bCombinatorics\b", text):
        return text
    lines = text.splitlines(keepends=True)
    first_namespace = next(
        (i for i, line in enumerate(lines) if line.startswith("namespace ")), None
    )
    if first_namespace is None:
        return text
    insert_at = first_namespace + 1
    i = first_namespace + 1
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped == "" or stripped.startswith("namespace "):
            if stripped.startswith("namespace "):
                insert_at = i + 1
            i += 1
            continue
        break
    lines.insert(insert_at, "\nopen Combinatorics\n")
    return "".join(lines)


def rewrite(path: Path) -> bool:
    original = path.read_text(encoding="utf-8")
    updated = original
    for old, new in IMPORT_REPLACEMENTS.items():
        updated = updated.replace(old, new)
    for old, new in QUALIFIED_REPLACEMENTS.items():
        updated = updated.replace(old, new)

    rel = path.relative_to(ROOT).as_posix()
    if rel.startswith("LeanCondensedMatter/SecondQuantization/") and PAIRING_TOKEN.search(updated):
        updated = insert_open_combinatorics(updated)

    if updated == original:
        return False
    path.write_text(updated, encoding="utf-8")
    print(rel)
    return True


def main() -> None:
    changed = sum(rewrite(path) for path in sorted(LEAN_ROOT.rglob("*.lean")))
    root_module = ROOT / "LeanCondensedMatter.lean"
    if root_module.exists():
        changed += rewrite(root_module)
    print(f"updated {changed} files")


if __name__ == "__main__":
    main()
