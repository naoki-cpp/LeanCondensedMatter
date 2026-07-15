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
- `mu_intCast_eq_complex` — `mu ℤ x y` cast to `ℂ` agrees with `mu ℂ x y` computed directly (same strong-induction technique). Added when `Combinatorics/MomentCumulant.lean` needed to reuse `mu_eq_prod_restrict`'s `ℤ`-coefficient content in a `ℂ`-coefficient setting without redoing the other three lemmas above for `ℂ`.

In `PartitionLattice.lean` itself, `restrict_self_part_eq_top` (`σ.restrict (σ.le hB) = ⊤` for `B ∈ σ.parts`) identifies `σ`'s own image under the fiber correspondence with the all-`⊤` element, closing the argument.

**Not yet done (Möbius formula):** the explicit closed-form factorial formula for each
`mu ℤ (π.restrict (σ.le hB)) ⊤` (a single-block Möbius function) is not yet proved — see
`notes/caveats.md` for attempted routes and next steps.

## Moment–cumulant inversion

Status: `proved`, in `LeanCondensedMatter/Combinatorics/MomentCumulant.lean`.

Goal: the moment/cumulant relation for a finite set `S`, defined as sums over `Finpartition S`,
and its inversion via Möbius inversion on the partition lattice — proved as a genuine **mutual**
inversion (both directions), not just one-sided. Coefficients fixed to `ℂ` throughout (matching
Track D's Fock-space side).

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
- **`Finpartition.cumulantFromMoment_momentFromCumulant`** —
  `cumulantFromMoment (momentFromCumulant κ) S = κ S`, for `S ≠ ⊥`. Proved by Möbius inversion on
  the partition lattice (`IncidenceAlgebra.moebius_inversion_bot`) evaluated at `⊤ : Finpartition
  S`, using `sum_Iic_partitionProduct_eq` to identify the "sum function" with `momentFromCumulant
  κ` applied blockwise.
- **`Finpartition.momentFromCumulant_cumulantFromMoment`** — the other direction:
  `momentFromCumulant (cumulantFromMoment m) S = m S`, for `S ≠ ⊥`. Needs two more pieces:
  - `IncidenceAlgebra.mu_intCast_eq_complex` (`IncidenceAlgebraMu.lean`) — `mu ℤ x y` cast to `ℂ`
    agrees with `mu ℂ x y` computed directly, by the same strong-induction argument as
    `mu_orderIso_apply` (the recursive definition of `mu` only uses `+`, `-`, `1`, so it commutes
    with the ring homomorphism `ℤ → ℂ`).
  - `Finpartition.mu_eq_prod_restrict_complex` (`PartitionLattice.lean`) — the `ℂ`-coefficient
    version of `mu_eq_prod_restrict`, obtained by casting the existing `ℤ` theorem rather than
    redoing the whole `mu_orderIso_apply`/`mu_subtype_le_apply`/`mu_pi_finset_apply` development
    for `ℂ`.
  - `Finpartition.sum_Iic_mu_partitionProduct_eq` — the reverse-direction analogue of
    `sum_Iic_partitionProduct_eq`: the `μ`-weighted sum over refinements of `π` equals the
    product, over `π`'s blocks, of `cumulantFromMoment m` applied to that block. Additionally uses
    `mu_eq_prod_restrict_complex` to identify `∏ B, mu ℂ (Q B) ⊤` with `mu ℂ ρ π` (`ρ := π.bind
    Q`), and `restrict_bind_eq` to identify `ρ.restrict (π.le B.2)` with `Q B`.
  - The main proof swaps the order of summation in `∑ π, ∑ ρ ≤ π, μ(ρ,π) · m-product(ρ)` to
    `∑ ρ, ∑ π ≥ ρ, μ(ρ,π) · m-product(ρ)`, then uses `IncidenceAlgebra.sum_Icc_mu_right` to
    telescope the inner sum to the indicator of `ρ = ⊤`.

**`S ≠ ⊥` is a genuine hypothesis, not a proof convenience, for both directions.** `Finpartition
⊥` is a one-element type (the only partition of the empty set is the empty one, with zero parts),
so `momentFromCumulant κ ⊥ = 1` regardless of `κ`, forcing `cumulantFromMoment (momentFromCumulant
κ) ⊥ = 1` too — the unrestricted equality would force `κ ⊥ = 1` for every `κ`, which is false. The
moment-cumulant relationship is simply not meaningful at the empty set.

**Not yet done (moment-cumulant):** connecting this finite-set combinatorial identity to actual
thermal expectation values / cumulants of physical observables (Track D), and the log-generating-
function / connected-contribution translation needed for the Linked Cluster Theorem itself.

## Moment factorization under independence (towards connected cumulants)

Status: `stated` — first (partition-level) step done, in
`LeanCondensedMatter/Combinatorics/CumulantFactorization.lean`.

Goal: the classical "cumulants vanish across independence" theorem, needed for the Linked Cluster
Theorem's "only connected diagrams survive in `log Z`" statement.

- `Finpartition.IsIndependentAcross m A B` — `m` factors independently across the disjoint pair
  `(A, B)`: `Disjoint A B ∧ m ⊥ = 1 ∧ ∀ T ≤ A ⊔ B, m T = m (T ⊓ A) * m (T ⊓ B)`. `m ⊥ = 1` is
  required explicitly, not derivable — the factorization alone only forces `m ⊥ ∈ {0, 1}`, and the
  `0` branch degenerates to `m ≡ 0`.
- `Finpartition.partitionProduct_restrict_eq_prod_inf` — a general fact about
  `Finpartition.restrict` (no independence needed): `partitionProduct m (π.restrict hb) = ∏ C ∈
  π.parts, m (C ⊓ b)`. Blocks with `C ⊓ b = ⊥` are absent from `(π.restrict hb).parts` but
  contribute a no-op `m ⊥ = 1` factor on the other side; among the rest, `C ↦ C ⊓ b` is injective
  (`eq_of_inf_ne_bot`, reused from `PartitionLattice.lean`) with image exactly
  `(π.restrict hb).parts`.
- **`Finpartition.partitionProduct_eq_mul_of_isIndependentAcross`** — the partition-level
  factorization: under `IsIndependentAcross m A B`, for any `π : Finpartition (A ⊔ B)`,
  `partitionProduct m π = partitionProduct m (π.restrict le_sup_left) * partitionProduct m
  (π.restrict le_sup_right)`.

**Not yet done:** the deeper cumulant-vanishing theorem itself, `cumulantFromMoment m (A ⊔ B) = 0`
under independence (for `A`, `B` both nonempty). This needs summing the partition-level
factorization above over all `π ∈ Finpartition (A ⊔ B)`, weighted by `μ(π, ⊤)` — but unlike the
moment-cumulant inversion proofs, the fiber of `π ↦ (π.restrict hA, π.restrict hB)` over a fixed
pair `(ρ_A, ρ_B)` is not a bijection: it's the set of ways to *partially match* blocks of `ρ_A`
with blocks of `ρ_B` (merging at most one block from each side per group). Summing `μ` over that
matching structure and showing it vanishes (except in degenerate cases) is a genuinely harder,
separate combinatorial argument — not attempted here.
