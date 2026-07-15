# Roadmap — Combinatorics (Track B)

See [notes/roadmap.md](../roadmap.md) for the status table and how this track fits into the overall plan. Independent of Track A — pure combinatorics, no physics content.

## Partition-lattice Möbius / moment-cumulant formula

Status: split into three sub-targets, tracked separately in `notes/roadmap.md`'s table:
- **Partition-lattice refinement/Möbius factorization — `proved`.**
- **Explicit partition-lattice Möbius formula (`(-1)^(n-1)(n-1)!`) — `stated`** (not yet proved; see
  "Not yet done" below).
- **Moment–cumulant inversion formula — `proved`**, in
  `LeanCondensedMatter/Combinatorics/MomentCumulant.lean`. See that section below.

Goal: formalize the general combinatorial moment-cumulant theorem on the lattice of set partitions (Möbius function of the partition lattice), in a form specializable to thermal expectation values.

`LocallyFiniteOrder (Finpartition s)` instance done (`LeanCondensedMatter/Combinatorics/PartitionLattice.lean`), letting Mathlib's `IncidenceAlgebra` Möbius machinery apply to the partition lattice.

**The refinement fiber decomposition is now done**, in the same file: `Finpartition.refinementsEquivFiberPartitions` — for `σ : Finpartition a`, an `Equiv` between `{π // π ≤ σ}` (partitions refining `σ`) and `∀ B : σ.parts, Finpartition (B : Finset α)` (an independent partition of each of `σ`'s parts). Built from:
- `bind_restrict_eq_of_le` — `σ.bind (fun B hB => π.restrict (σ.le hB)) = π` for `π ≤ σ`.
- `restrict_bind_eq` — the converse, `(σ.bind Q).restrict (σ.le hB) = Q B hB`.
- `bind_le` — `σ.bind Q ≤ σ` (needed for the `Equiv`'s inverse to land in the subtype).
- `mem_restrict_iff`/`eq_of_inf_ne_bot` — supporting lemmas, factored out for reuse (unfolding `Finpartition.restrict`'s membership condition, and the "two parts of a partition sharing a nonempty overlap must coincide" fact both directions need).

This exhibits the interval `[⊥, σ]` in the partition lattice as (in bijection with) the product `Π B ∈ σ.parts, Finpartition B` — the structural fact underlying the moment-cumulant / Möbius-inversion formula.

**The `Equiv` is now upgraded to an order isomorphism**: `Finpartition.refinementsOrderIsoFiberPartitions`, relating `≤` on `{π // π ≤ σ}` (refinement, inherited from `Finpartition a`) to the pointwise product order on `∀ B, Finpartition B`. Built from `restrict_mono` (`P ≤ P' → P.restrict hb ≤ P'.restrict hb`) for the easy direction, and, for the other, testing membership of a part `A` of `π` at the `σ`-part `B` containing it and transporting the pointwise hypothesis there via `mem_restrict_iff`.

**The Möbius function now factors as a product over `σ`'s parts**: `Finpartition.mu_eq_prod_restrict` — for `π ≤ σ`, `mu ℤ π σ = ∏ B ∈ σ.parts, mu ℤ (π.restrict (σ.le hB)) ⊤` (where `⊤ : Finpartition B` is the indiscrete partition of `B`). This is the moment-cumulant formula's structural core. Built from `refinementsOrderIsoFiberPartitions` plus three general (partition-independent) facts about `IncidenceAlgebra.mu`, new in `LeanCondensedMatter/Combinatorics/IncidenceAlgebraMu.lean` (coefficients fixed to `ℤ`, since that's all this application needs):
- `mu_orderIso_apply` — `mu` is invariant under order isomorphism (strong induction on `Icc` cardinality, mirroring `mu`'s own recursive definition).
- `mu_subtype_le_apply` — `mu` computed inside a down-set `{t // t ≤ z}` agrees with the ambient `mu`. Needs `[Fintype α]` for a `LocallyFiniteOrder` instance on the down-set (`instLocallyFiniteOrderSubtypeLe`) — satisfied by `Finpartition a`, already `Fintype`.
- `mu_pi_finset_apply` — `mu` on a finite dependent product `∀ i : t, β i` is the product of the factors' `mu`'s. Proved by induction on `t : Finset ι`, splitting off one index at a time via `piInsertOrderIso` (an order isomorphism `∀ i : insert j s, β i ≃o β j × ∀ i : s, β i`) combined with Mathlib's `IncidenceAlgebra.mu_prod_mu`.

In `PartitionLattice.lean` itself, `restrict_self_part_eq_top` (`σ.restrict (σ.le hB) = ⊤` for `B ∈ σ.parts`) identifies `σ`'s own image under the fiber correspondence with the all-`⊤` element, closing the argument.

**Not yet done (Möbius formula):** the explicit closed-form factorial formula for each
`mu ℤ (π.restrict (σ.le hB)) ⊤` (a single-block Möbius function) is not yet proved — see
`notes/caveats.md` for attempted routes and next steps.

## Moment–cumulant inversion

Status: `proved`, in `LeanCondensedMatter/Combinatorics/MomentCumulant.lean`.

Goal: the moment/cumulant relation for a finite set `S`, defined as sums over `Finpartition S`,
and its inversion via Möbius inversion on the partition lattice. Coefficients fixed to `ℂ`
throughout (using `IncidenceAlgebra.mu ℂ` directly, not `mu ℤ` cast — avoids an unneeded
cast-compatibility lemma and matches the coefficient field on Track D's Fock-space side).

- `Finpartition.partitionProduct f π := ∏ B ∈ π.parts, f B` — the product of `f` over a
  partition's blocks.
- `Finpartition.momentFromCumulant κ S := ∑ π : Finpartition S, partitionProduct κ π` — the
  moment associated to a cumulant `κ`.
- `Finpartition.cumulantFromMoment m S := ∑ π : Finpartition S, mu ℂ π ⊤ * partitionProduct m π`
  — the cumulant recovered from a moment `m` via the partition lattice's Möbius function.
- `Finpartition.partitionProduct_bind` — the product over a `bind`-glued partition factors as a
  product over the coarser partition's blocks of the product over each block's own
  sub-partition. Proved via `Finset.prod_biUnion` (disjointness of `Q B`'s parts across distinct
  `B`, mirroring `Finpartition.card_bind`'s own disjointness argument).
- `Finpartition.sum_Iic_partitionProduct_eq` — the sum, over all refinements `ρ ≤ π`, of the full
  product equals the product over `π`'s blocks of `momentFromCumulant κ` applied to that block.
  Combines `refinementsEquivFiberPartitions` (reindexing the sum via the refinement-fiber
  bijection), `partitionProduct_bind`, and the "sum of a product of independent choices is a
  product of sums" identity (`Finset.prod_univ_sum`).
- **`Finpartition.cumulantFromMoment_momentFromCumulant`** — the main theorem:
  `cumulantFromMoment (momentFromCumulant κ) S = κ S`, for `S ≠ ⊥`. Proved by Möbius inversion on
  the partition lattice (`IncidenceAlgebra.moebius_inversion_bot`) evaluated at `⊤ : Finpartition
  S`, using `sum_Iic_partitionProduct_eq` to identify the "sum function" with `momentFromCumulant
  κ` applied blockwise.

**`S ≠ ⊥` is a genuine hypothesis, not a proof convenience.** `Finpartition ⊥` is a one-element
type (the only partition of the empty set is the empty one, with zero parts), so
`momentFromCumulant κ ⊥ = 1` regardless of `κ`, forcing `cumulantFromMoment (momentFromCumulant
κ) ⊥ = 1` too — the unrestricted equality would force `κ ⊥ = 1` for every `κ`, which is false.
The moment-cumulant relationship is simply not meaningful at the empty set.

**Not yet done (moment-cumulant):** connecting this finite-set combinatorial identity to actual
thermal expectation values / cumulants of physical observables (Track D), and the log-generating-
function / connected-contribution translation needed for the Linked Cluster Theorem itself.
