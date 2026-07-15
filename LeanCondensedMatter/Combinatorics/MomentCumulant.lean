import LeanCondensedMatter.Combinatorics.PartitionLattice
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Moment–cumulant inversion on the partition lattice

The moment/cumulant relation for a finite set `S`, defined as sums over `Finpartition S`, and its
Möbius inversion. This is the combinatorial core underlying the physical moment-cumulant theorem
(and, eventually, the Linked Cluster Theorem) — see `notes/roadmaps/combinatorics.md`.

Coefficients are fixed to `ℂ` throughout (rather than a general ring, and using
`IncidenceAlgebra.mu ℂ` directly rather than `mu ℤ` cast to `ℂ`), matching the coefficient field
used on the Fock-space side of the project (Track D).
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

/-- **The product of `f` over the parts of a partition `π`.** -/
noncomputable def partitionProduct (f : Finset α → ℂ) {S : Finset α} (π : Finpartition S) : ℂ :=
  ∏ B ∈ π.parts, f B

/-- **The moment associated to a cumulant `κ`**, on a finite set `S`: the sum, over every
partition of `S`, of the product of `κ` over that partition's blocks. -/
noncomputable def momentFromCumulant (κ : Finset α → ℂ) (S : Finset α) : ℂ :=
  ∑ π : Finpartition S, partitionProduct κ π

/-- **The cumulant recovered from a moment `m`**, via Möbius inversion on the partition lattice:
the sum, over every partition of `S`, of the Möbius function `μ(π, ⊤)` times the product of `m`
over `π`'s blocks. -/
noncomputable def cumulantFromMoment (m : Finset α → ℂ) (S : Finset α) : ℂ :=
  ∑ π : Finpartition S, mu ℂ π ⊤ * partitionProduct m π

@[simp]
theorem partitionProduct_top {S : Finset α} (hS : S ≠ ⊥) (f : Finset α → ℂ) :
    partitionProduct f (⊤ : Finpartition S) = f S := by
  have hparts : (⊤ : Finpartition S).parts = {S} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, fun d hd => Finset.mem_singleton.1 (Finpartition.parts_top_subset S hd)⟩
    obtain ⟨x, hx⟩ := (Finpartition.parts_nonempty_iff (P := (⊤ : Finpartition S))).2 hS
    rwa [Finset.mem_singleton.1 (Finpartition.parts_top_subset S hx)] at hx
  rw [partitionProduct, hparts, Finset.prod_singleton]

/-- **The product over a `bind`-glued partition factors as a product over blocks of the coarser
partition, of the product over that block's own sub-partition.** The combinatorial heart of the
moment-cumulant block-factorization argument. -/
theorem partitionProduct_bind (f : Finset α → ℂ) {S : Finset α} (σ : Finpartition S)
    (Q : ∀ B ∈ σ.parts, Finpartition B) :
    partitionProduct f (σ.bind Q) = ∏ B ∈ σ.parts.attach, partitionProduct f (Q B.1 B.2) := by
  classical
  change ∏ C ∈ (σ.bind Q).parts, f C = _
  apply Finset.prod_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun, Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne, Subtype.mk_eq_mk] at hbc
  exact (Q b hb).ne_bot hdb
    (eq_bot_iff.2 <| (le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans <|
      (σ.disjoint hb hc hbc).le_bot)

/-- **The sum over refinements of `π` (partitions `ρ ≤ π`) of the full product equals the
product, over `π`'s blocks, of the moment `momentFromCumulant κ` applied to that block.**
Combines the refinement fiber decomposition (`refinementsEquivFiberPartitions`) with
`partitionProduct_bind` and the standard "sum of a product of independent choices is a product of
sums" identity (`Finset.prod_sum`). -/
theorem sum_Iic_partitionProduct_eq (κ : Finset α → ℂ) {S : Finset α} (π : Finpartition S) :
    (∑ ρ ∈ Finset.Iic π, partitionProduct κ ρ) = partitionProduct (momentFromCumulant κ) π := by
  classical
  have hstep1 : (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, partitionProduct κ ρ.1) =
      ∏ B : π.parts, momentFromCumulant κ (B : Finset α) := by
    rw [← Equiv.sum_comp (refinementsEquivFiberPartitions π).symm
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => partitionProduct κ ρ.1)]
    have hpt : ∀ Q : ∀ B : π.parts, Finpartition (B : Finset α),
        partitionProduct κ ((refinementsEquivFiberPartitions π).symm Q).1 =
          ∏ B : π.parts, partitionProduct κ (Q B) := fun Q => by
      change partitionProduct κ (π.bind fun B hB => Q ⟨B, hB⟩) = _
      rw [partitionProduct_bind κ π (fun B hB => Q ⟨B, hB⟩), ← Finset.univ_eq_attach]
    simp_rw [hpt]
    have hdist := Finset.prod_univ_sum
      (fun B : π.parts => (Finset.univ : Finset (Finpartition (B : Finset α))))
      (fun B q => partitionProduct κ q)
    rw [Fintype.piFinset_univ] at hdist
    exact hdist.symm
  have hstep2 : (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, partitionProduct κ ρ.1) =
      ∑ ρ ∈ Finset.Iic π, partitionProduct κ ρ := by
    rw [← Finset.sum_coe_sort (Finset.Iic π) (partitionProduct κ)]
    refine Fintype.sum_equiv (Equiv.subtypeEquivRight (fun ρ => Finset.mem_Iic (a := π).symm))
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => partitionProduct κ ρ.1)
      (fun ρ : {ρ : Finpartition S // ρ ∈ Finset.Iic π} => partitionProduct κ ρ.1) fun x => ?_
    rw [Equiv.subtypeEquivRight_apply]
  rw [← hstep2, hstep1, partitionProduct, Finset.prod_coe_sort π.parts (momentFromCumulant κ)]

/-- **Moment–cumulant inversion.** Recovering a cumulant `κ` from its associated moment
`momentFromCumulant κ` via `cumulantFromMoment` returns `κ` exactly. Proved by Möbius inversion
on the partition lattice (`IncidenceAlgebra.moebius_inversion_bot`), using
`sum_Iic_partitionProduct_eq` to identify the "sum function" at each partition `π` with
`momentFromCumulant κ` applied blockwise.

**`S ≠ ⊥` is a genuine hypothesis, not just a proof convenience:** `Finpartition ⊥` is a
one-element type (the only partition of the empty set is the empty one, with zero parts), so
`momentFromCumulant κ ⊥ = 1` regardless of `κ`, and hence `cumulantFromMoment (momentFromCumulant
κ) ⊥ = 1` regardless of `κ` too — the claimed equality would force `κ ⊥ = 1` for every `κ`, which
is false. The moment-cumulant relationship is simply not meaningful at the empty set. -/
theorem cumulantFromMoment_momentFromCumulant (κ : Finset α → ℂ) {S : Finset α} (hS : S ≠ ⊥) :
    cumulantFromMoment (momentFromCumulant κ) S = κ S := by
  classical
  have hIic : Finset.Iic (⊤ : Finpartition S) = Finset.univ := by
    ext π; simp
  have hmain := moebius_inversion_bot (α := Finpartition S)
    (fun π => partitionProduct κ π) (fun σ => ∑ π ∈ Finset.Iic σ, partitionProduct κ π)
    (fun _ => rfl) (⊤ : Finpartition S)
  rw [hIic] at hmain
  rw [partitionProduct_top hS κ] at hmain
  rw [hmain, cumulantFromMoment]
  exact Finset.sum_congr rfl fun π _ => by rw [sum_Iic_partitionProduct_eq κ π]

/-- **The reverse-direction analogue of `sum_Iic_partitionProduct_eq`.** The `μ`-weighted sum
over refinements of `π` equals the product, over `π`'s blocks, of the cumulant
`cumulantFromMoment m` applied to that block. In addition to `refinementsEquivFiberPartitions`
and `partitionProduct_bind`, uses `mu_eq_prod_restrict_complex` to identify `∏ B, mu ℂ (Q B) ⊤`
with `mu ℂ ρ π` for `ρ := π.bind Q`, and `restrict_bind_eq` to identify `ρ.restrict (π.le B.2)`
with `Q B`. -/
theorem sum_Iic_mu_partitionProduct_eq (m : Finset α → ℂ) {S : Finset α} (π : Finpartition S) :
    (∑ ρ ∈ Finset.Iic π, mu ℂ ρ π * partitionProduct m ρ) =
      partitionProduct (cumulantFromMoment m) π := by
  classical
  have hstep1 : (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, mu ℂ ρ.1 π * partitionProduct m ρ.1) =
      ∏ B : π.parts, cumulantFromMoment m (B : Finset α) := by
    rw [← Equiv.sum_comp (refinementsEquivFiberPartitions π).symm
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => mu ℂ ρ.1 π * partitionProduct m ρ.1)]
    have hpt : ∀ Q : ∀ B : π.parts, Finpartition (B : Finset α),
        mu ℂ ((refinementsEquivFiberPartitions π).symm Q).1 π *
            partitionProduct m ((refinementsEquivFiberPartitions π).symm Q).1 =
          ∏ B : π.parts, (mu ℂ (Q B) ⊤ * partitionProduct m (Q B)) := fun Q => by
      change mu ℂ (π.bind fun B hB => Q ⟨B, hB⟩) π *
          partitionProduct m (π.bind fun B hB => Q ⟨B, hB⟩) = _
      rw [partitionProduct_bind m π (fun B hB => Q ⟨B, hB⟩), ← Finset.univ_eq_attach,
        mu_eq_prod_restrict_complex (bind_le π (fun B hB => Q ⟨B, hB⟩)), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun B _ => by
        rw [restrict_bind_eq π (fun B hB => Q ⟨B, hB⟩) B.2]
    simp_rw [hpt]
    have hdist := Finset.prod_univ_sum
      (fun B : π.parts => (Finset.univ : Finset (Finpartition (B : Finset α))))
      (fun B q => mu ℂ q ⊤ * partitionProduct m q)
    rw [Fintype.piFinset_univ] at hdist
    exact hdist.symm
  have hstep2 : (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, mu ℂ ρ.1 π * partitionProduct m ρ.1) =
      ∑ ρ ∈ Finset.Iic π, mu ℂ ρ π * partitionProduct m ρ := by
    rw [← Finset.sum_coe_sort (Finset.Iic π) (fun ρ => mu ℂ ρ π * partitionProduct m ρ)]
    refine Fintype.sum_equiv (Equiv.subtypeEquivRight (fun ρ => Finset.mem_Iic (a := π).symm))
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => mu ℂ ρ.1 π * partitionProduct m ρ.1)
      (fun ρ : {ρ : Finpartition S // ρ ∈ Finset.Iic π} => mu ℂ ρ.1 π * partitionProduct m ρ.1)
      fun x => ?_
    rw [Equiv.subtypeEquivRight_apply]
  rw [← hstep2, hstep1, partitionProduct, Finset.prod_coe_sort π.parts (cumulantFromMoment m)]

/-- **Moment–cumulant inversion, the other direction.** Recovering a moment `m` from its
associated cumulant `cumulantFromMoment m` via `momentFromCumulant` returns `m` exactly. Together
with `cumulantFromMoment_momentFromCumulant`, this closes the moment-cumulant relationship as a
genuine mutual inversion, not just a one-sided one.

Proved by swapping the order of summation in `∑ π, ∑ ρ ≤ π, μ(ρ,π) m-product(ρ)` (via
`sum_Iic_mu_partitionProduct_eq`) to `∑ ρ, ∑ π ≥ ρ, μ(ρ,π) m-product(ρ)`, then using
`IncidenceAlgebra.sum_Icc_mu_right` to telescope the inner sum to the indicator of `ρ = ⊤`. -/
theorem momentFromCumulant_cumulantFromMoment (m : Finset α → ℂ) {S : Finset α} (hS : S ≠ ⊥) :
    momentFromCumulant (cumulantFromMoment m) S = m S := by
  classical
  have hswap : (∑ π : Finpartition S, ∑ ρ ∈ Finset.Iic π, mu ℂ ρ π * partitionProduct m ρ) =
      ∑ ρ : Finpartition S,
        ∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu ℂ ρ π * partitionProduct m ρ := by
    have e1 : ∀ π : Finpartition S, (∑ ρ ∈ Finset.Iic π, mu ℂ ρ π * partitionProduct m ρ) =
        ∑ ρ : Finpartition S, if ρ ≤ π then mu ℂ ρ π * partitionProduct m ρ else 0 := by
      intro π
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext ρ; simp) fun _ _ => rfl
    have e2 : ∀ ρ : Finpartition S,
        (∑ π : Finpartition S, if ρ ≤ π then mu ℂ ρ π * partitionProduct m ρ else 0) =
          ∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu ℂ ρ π * partitionProduct m ρ := by
      intro ρ
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext π; simp) fun _ _ => rfl
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [e2]
  have htele : ∀ ρ : Finpartition S,
      (∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu ℂ ρ π * partitionProduct m ρ) =
        (if ρ = ⊤ then 1 else 0) * partitionProduct m ρ := by
    intro ρ
    rw [← Finset.sum_mul, sum_Icc_mu_right]
  rw [momentFromCumulant]
  simp_rw [← sum_Iic_mu_partitionProduct_eq m]
  rw [hswap]
  simp_rw [htele]
  simp [partitionProduct_top hS m]

end Finpartition
