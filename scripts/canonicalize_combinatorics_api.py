from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

MOVES = {
    "LeanCondensedMatter/Combinatorics/BinaryShuffle.lean":
        "LeanCondensedMatter/Combinatorics/Shuffle/Binary.lean",
    "LeanCondensedMatter/Combinatorics/BinaryShuffleSlots.lean":
        "LeanCondensedMatter/Combinatorics/Shuffle/BinarySlots.lean",
    "LeanCondensedMatter/Combinatorics/BinaryShuffleSlotEquiv.lean":
        "LeanCondensedMatter/Combinatorics/Shuffle/BinaryEquiv.lean",
    "LeanCondensedMatter/Combinatorics/FamilySlotShuffle.lean":
        "LeanCondensedMatter/Combinatorics/Shuffle/Family.lean",
    "LeanCondensedMatter/Combinatorics/FamilySlotShuffleDecomposition.lean":
        "LeanCondensedMatter/Combinatorics/Shuffle/FamilyDecomposition.lean",
    "LeanCondensedMatter/Combinatorics/Common/FinsetProduct.lean":
        "LeanCondensedMatter/Combinatorics/Finset/Product.lean",
}

IMPORT_REPLACEMENTS = {
    "LeanCondensedMatter.Combinatorics.BinaryShuffleSlotEquiv":
        "LeanCondensedMatter.Combinatorics.Shuffle.BinaryEquiv",
    "LeanCondensedMatter.Combinatorics.BinaryShuffleSlots":
        "LeanCondensedMatter.Combinatorics.Shuffle.BinarySlots",
    "LeanCondensedMatter.Combinatorics.BinaryShuffle":
        "LeanCondensedMatter.Combinatorics.Shuffle.Binary",
    "LeanCondensedMatter.Combinatorics.FamilySlotShuffleDecomposition":
        "LeanCondensedMatter.Combinatorics.Shuffle.FamilyDecomposition",
    "LeanCondensedMatter.Combinatorics.FamilySlotShuffle":
        "LeanCondensedMatter.Combinatorics.Shuffle.Family",
    "LeanCondensedMatter.Combinatorics.Common.FinsetProduct":
        "LeanCondensedMatter.Combinatorics.Finset.Product",
}

IDENTIFIER_REPLACEMENTS = [
    (r"\bmem_allPairings\b", "mem_allPerfectPairings"),
    (r"\ballPairings\b", "allPerfectPairings"),
    (r"\bdecidableIsPairing\b", "decidableIsPerfectPairing"),
    (r"\bpairingEquivSubtype\b", "perfectPairingEquivSubtype"),
    (r"\bIsPairing\b", "IsPerfectPairing"),
    (r"\bPairing\b", "PerfectPairing"),
]


def move_files() -> None:
    for old_rel, new_rel in MOVES.items():
        old = ROOT / old_rel
        new = ROOT / new_rel
        if not old.exists():
            continue
        if new.exists():
            raise RuntimeError(f"destination already exists: {new_rel}")
        new.parent.mkdir(parents=True, exist_ok=True)
        old.rename(new)
        print(f"move {old_rel} -> {new_rel}")


def rewrite(path: Path) -> bool:
    original = path.read_text(encoding="utf-8")
    updated = original
    for old, new in IMPORT_REPLACEMENTS.items():
        updated = updated.replace(old, new)
    for pattern, replacement in IDENTIFIER_REPLACEMENTS:
        updated = re.sub(pattern, replacement, updated)
    if updated == original:
        return False
    path.write_text(updated, encoding="utf-8")
    print(path.relative_to(ROOT).as_posix())
    return True


def main() -> None:
    move_files()
    changed = 0
    for extension in ("*.lean", "*.md"):
        for path in sorted(ROOT.rglob(extension)):
            if ".lake" in path.parts or ".git" in path.parts:
                continue
            changed += rewrite(path)
    print(f"rewrote {changed} files")


if __name__ == "__main__":
    main()
