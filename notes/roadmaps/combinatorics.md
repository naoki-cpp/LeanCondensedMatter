# Roadmap — Combinatorics (Track B)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan. Independent of Track A — pure combinatorics, no physics content.

## Partition-lattice Möbius / moment-cumulant formula

Status: `stated`.

Goal: formalize the general combinatorial moment-cumulant theorem on the lattice of set partitions (Möbius function of the partition lattice), in a form specializable to thermal expectation values.

`LocallyFiniteOrder (Finpartition s)` instance done (`LeanCondensedMatter/Combinatorics/PartitionLattice.lean`), letting Mathlib's `IncidenceAlgebra` Möbius machinery apply to the partition lattice.

**The refinement fiber decomposition is now done**, in the same file: `Finpartition.refinementsEquivFiberPartitions` — for `σ : Finpartition a`, an `Equiv` between `{π // π ≤ σ}` (partitions refining `σ`) and `∀ B : σ.parts, Finpartition (B : Finset α)` (an independent partition of each of `σ`'s parts). Built from:
- `bind_restrict_eq_of_le` — `σ.bind (fun B hB => π.restrict (σ.le hB)) = π` for `π ≤ σ`.
- `restrict_bind_eq` — the converse, `(σ.bind Q).restrict (σ.le hB) = Q B hB`.
- `bind_le` — `σ.bind Q ≤ σ` (needed for the `Equiv`'s inverse to land in the subtype).
- `mem_restrict_iff`/`eq_of_inf_ne_bot` — supporting lemmas, factored out for reuse (unfolding `Finpartition.restrict`'s membership condition, and the "two parts of a partition sharing a nonempty overlap must coincide" fact both directions need).

This exhibits the interval `[⊥, σ]` in the partition lattice as (in bijection with) the product `Π B ∈ σ.parts, Finpartition B` — the structural fact underlying the moment-cumulant / Möbius-inversion formula.

**The `Equiv` is now upgraded to an order isomorphism**: `Finpartition.refinementsOrderIsoFiberPartitions`, relating `≤` on `{π // π ≤ σ}` (refinement, inherited from `Finpartition a`) to the pointwise product order on `∀ B, Finpartition B`. Built from `restrict_mono` (`P ≤ P' → P.restrict hb ≤ P'.restrict hb`) for the easy direction, and, for the other, testing membership of a part `A` of `π` at the `σ`-part `B` containing it and transporting the pointwise hypothesis there via `mem_restrict_iff`.

**Not yet done:** the closed-form Möbius formula itself is not yet proved — see `notes/caveats.md` for attempted routes and next steps.
