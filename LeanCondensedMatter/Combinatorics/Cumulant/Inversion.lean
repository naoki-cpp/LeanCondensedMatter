import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import LeanCondensedMatter.Combinatorics.SetPartition.Mobius

set_option linter.style.header false

/-!
# Moment–cumulant inversion on the partition lattice

The finite-set moment transform is defined over commutative semirings in
`Combinatorics/Cumulant/Moment.lean`. This module adds the Möbius-inverse cumulant transform and the
pointwise inversion theorems, which require a commutative ring. Their low-level pointwise inversion
requires a nonempty finite set; a normalized bundled API removes that side condition in
`Combinatorics/Cumulant/Normalized.lean`.
-/

open IncidenceAlgebra

variable {α R : Type*} [DecidableEq α] [CommRing R]

namespace Finpartition

/-- Cumulant transform obtained by Möbius inversion on the partition lattice. -/
noncomputable def cumulantFromMoment (m : Finset α → R) (S : Finset α) : R :=
  ∑ π : Finpartition S, mu R π ⊤ * partitionProduct m π

@[simp]
theorem partitionProduct_top {S : Finset α} (hS : S ≠ ∅) (f : Finset α → R) :
    partitionProduct f (⊤ : Finpartition S) = f S := by
  have hparts : (⊤ : Finpartition S).parts = {S} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, fun d hd => Finset.mem_singleton.1 (Finpartition.parts_top_subset S hd)⟩
    obtain ⟨x, hx⟩ := (Finpartition.parts_nonempty_iff (P := (⊤ : Finpartition S))).2 hS
    rwa [Finset.mem_singleton.1 (Finpartition.parts_top_subset S hx)] at hx
  rw [partitionProduct, hparts, Finset.prod_singleton]

/-- Block products factor over a partition constructed by `bind`. -/
theorem partitionProduct_bind (f : Finset α → R) {S : Finset α} (σ : Finpartition S)
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

/-- Sum of block products over refinements factors into blockwise moments. -/
theorem sum_Iic_partitionProduct_eq (κ : Finset α → R) {S : Finset α} (π : Finpartition S) :
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

/-- Pointwise Möbius inversion, away from the empty finite set. -/
theorem cumulantFromMoment_momentFromCumulant (κ : Finset α → R)
    {S : Finset α} (hS : S ≠ ⊥) :
    cumulantFromMoment (momentFromCumulant κ) S = κ S := by
  classical
  have hIic : Finset.Iic (⊤ : Finpartition S) = Finset.univ := by
    ext π
    simp
  have hmain := moebius_inversion_bot (α := Finpartition S)
    (fun π => partitionProduct κ π) (fun σ => ∑ π ∈ Finset.Iic σ, partitionProduct κ π)
    (fun _ => rfl) (⊤ : Finpartition S)
  rw [hIic] at hmain
  rw [partitionProduct_top hS κ] at hmain
  rw [hmain, cumulantFromMoment]
  exact Finset.sum_congr rfl fun π _ => by rw [sum_Iic_partitionProduct_eq κ π]

/-- Möbius-weighted refinement sums factor into blockwise cumulants. -/
theorem sum_Iic_mu_partitionProduct_eq (m : Finset α → R)
    {S : Finset α} (π : Finpartition S) :
    (∑ ρ ∈ Finset.Iic π, mu R ρ π * partitionProduct m ρ) =
      partitionProduct (cumulantFromMoment m) π := by
  classical
  have hstep1 :
      (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, mu R ρ.1 π * partitionProduct m ρ.1) =
        ∏ B : π.parts, cumulantFromMoment m (B : Finset α) := by
    rw [← Equiv.sum_comp (refinementsEquivFiberPartitions π).symm
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => mu R ρ.1 π * partitionProduct m ρ.1)]
    have hpt : ∀ Q : ∀ B : π.parts, Finpartition (B : Finset α),
        mu R ((refinementsEquivFiberPartitions π).symm Q).1 π *
            partitionProduct m ((refinementsEquivFiberPartitions π).symm Q).1 =
          ∏ B : π.parts, (mu R (Q B) ⊤ * partitionProduct m (Q B)) := fun Q => by
      change mu R (π.bind fun B hB => Q ⟨B, hB⟩) π *
          partitionProduct m (π.bind fun B hB => Q ⟨B, hB⟩) = _
      rw [partitionProduct_bind m π (fun B hB => Q ⟨B, hB⟩), ← Finset.univ_eq_attach,
        mu_eq_prod_restrict (R := R) (bind_le π (fun B hB => Q ⟨B, hB⟩)),
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun B _ => by
        rw [restrict_bind_eq π (fun B hB => Q ⟨B, hB⟩) B.2]
    simp_rw [hpt]
    have hdist := Finset.prod_univ_sum
      (fun B : π.parts => (Finset.univ : Finset (Finpartition (B : Finset α))))
      (fun B q => mu R q ⊤ * partitionProduct m q)
    rw [Fintype.piFinset_univ] at hdist
    exact hdist.symm
  have hstep2 :
      (∑ ρ : {ρ : Finpartition S // ρ ≤ π}, mu R ρ.1 π * partitionProduct m ρ.1) =
        ∑ ρ ∈ Finset.Iic π, mu R ρ π * partitionProduct m ρ := by
    rw [← Finset.sum_coe_sort (Finset.Iic π) (fun ρ => mu R ρ π * partitionProduct m ρ)]
    refine Fintype.sum_equiv (Equiv.subtypeEquivRight (fun ρ => Finset.mem_Iic (a := π).symm))
      (fun ρ : {ρ : Finpartition S // ρ ≤ π} => mu R ρ.1 π * partitionProduct m ρ.1)
      (fun ρ : {ρ : Finpartition S // ρ ∈ Finset.Iic π} =>
        mu R ρ.1 π * partitionProduct m ρ.1) fun x => ?_
    rw [Equiv.subtypeEquivRight_apply]
  rw [← hstep2, hstep1, partitionProduct, Finset.prod_coe_sort π.parts (cumulantFromMoment m)]

/-- Reverse pointwise inversion, away from the empty finite set. -/
theorem momentFromCumulant_cumulantFromMoment (m : Finset α → R)
    {S : Finset α} (hS : S ≠ ⊥) :
    momentFromCumulant (cumulantFromMoment m) S = m S := by
  classical
  have hswap :
      (∑ π : Finpartition S,
        ∑ ρ ∈ Finset.Iic π, mu R ρ π * partitionProduct m ρ) =
      ∑ ρ : Finpartition S,
        ∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu R ρ π * partitionProduct m ρ := by
    have e1 : ∀ π : Finpartition S,
        (∑ ρ ∈ Finset.Iic π, mu R ρ π * partitionProduct m ρ) =
          ∑ ρ : Finpartition S, if ρ ≤ π then mu R ρ π * partitionProduct m ρ else 0 := by
      intro π
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext ρ; simp) fun _ _ => rfl
    have e2 : ∀ ρ : Finpartition S,
        (∑ π : Finpartition S, if ρ ≤ π then mu R ρ π * partitionProduct m ρ else 0) =
          ∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu R ρ π * partitionProduct m ρ := by
      intro ρ
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext π; simp) fun _ _ => rfl
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [e2]
  have htele : ∀ ρ : Finpartition S,
      (∑ π ∈ Finset.Icc ρ (⊤ : Finpartition S), mu R ρ π * partitionProduct m ρ) =
        (if ρ = ⊤ then 1 else 0) * partitionProduct m ρ := by
    intro ρ
    rw [← Finset.sum_mul, sum_Icc_mu_right]
  rw [momentFromCumulant]
  simp_rw [← sum_Iic_mu_partitionProduct_eq m]
  rw [hswap]
  simp_rw [htele]
  simp [partitionProduct_top hS m]

end Finpartition
