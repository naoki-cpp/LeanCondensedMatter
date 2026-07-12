# Roadmap — Combinatorics (Track B)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan. Independent of Track A — pure combinatorics, no physics content.

## Partition-lattice Möbius / moment-cumulant formula

Status: `stated`.

Goal: formalize the general combinatorial moment-cumulant theorem on the lattice of set partitions (Möbius function of the partition lattice), in a form specializable to thermal expectation values.

`LocallyFiniteOrder (Finpartition s)` instance done (`LeanCondensedMatter/Combinatorics/PartitionLattice.lean`), letting Mathlib's `IncidenceAlgebra` Möbius machinery apply to the partition lattice. `Finpartition.bind_le`/`bind_restrict_eq_of_le` done (the `π ≤ σ ↔ (block-restrictions of π)` correspondence needed for the moment-cumulant sum decomposition, one direction). The closed-form Möbius formula itself is not yet proved — see `notes/caveats.md` for attempted routes and next steps.
