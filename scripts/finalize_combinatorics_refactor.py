from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ROADMAP = ROOT / "notes/roadmaps/combinatorics.md"

MARKER = "## Refactored module architecture"
SECTION = r'''

## Refactored module architecture

The combinatorics layer is now organized by mathematical responsibility rather than by the
physics feature that first needed a lemma:

- `Combinatorics/FiniteIndex/`: deletion and reindexing of finite positions;
- `Combinatorics/Shuffle/`: recursive binary shuffles, ambient-slot shuffles, finite-family
  shuffles, and their decompositions;
- `Combinatorics/IncidenceAlgebra/`: coefficient-generic structural facts about the Möbius
  function;
- `Combinatorics/SetPartition/`: refinement fibers, partition-lattice Möbius factorization, and
  distinguished-block decomposition;
- `Combinatorics/Cumulant/`: coefficient-generic inversion, normalized set functions,
  independence, and connected decompositions;
- `Combinatorics/PerfectPairing/`: `Combinatorics.PerfectPairing`, relabeling, crossing parity,
  and first-pair recursion.

Analytic constructions no longer live in the combinatorics layer. Shuffled integrands and their
continuity are under `Analysis/OrderedSimplex/`, while the formal-power-series/cumulant bridge is
under `Analysis/PowerSeries/`.

The public entry point is `LeanCondensedMatter.Combinatorics`. Old module paths, the old
`SecondQuantization.Common.BlochDeDominicis.Pairing` namespace, and compatibility aliases are not
retained.
'''


def main() -> None:
    text = ROADMAP.read_text(encoding="utf-8")
    if MARKER not in text:
        ROADMAP.write_text(text.rstrip() + SECTION + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
