import LeanCondensedMatter.Combinatorics.SetPartition.Refinement
import LeanCondensedMatter.Combinatorics.IncidenceAlgebra.Mobius

set_option linter.style.header false

/-!
# Coarsenings of a finite set partition

A coarsening of a partition `π` is equivalently a partition of the finite set `π.parts`. This is the
upper-interval counterpart of the refinement-fiber decomposition.
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

variable {a : Finset α}

private def blockFiber (π : Finpartition a) (B : Finset α) : Finset (Finset α) :=
  π.parts.filter fun A => A ≤ B

private def flattenBlock (C : Finset (Finset α)) : Finset α :=
  C.biUnion id

/-- A coarsening of `π` induces a partition of the block set of `π`. -/
private def quotientByCoarsening (π σ : Finpartition a) (hπσ : π ≤ σ) :
    Finpartition π.parts := by
  classical
  refine Finpartition.ofExistsUnique
    (σ.parts.image (blockFiber π)) ?_ ?_ ?_
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.filter_subset _ _
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hπσ hA
    refine ⟨blockFiber π B, ⟨Finset.mem_image.mpr ⟨B, hB, rfl⟩,
      Finset.mem_filter.mpr ⟨hA, hAB⟩⟩, ?_⟩
    intro C hC
    obtain ⟨hC, hAC⟩ := hC
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hC
    have hAB' : A ≤ B' := (Finset.mem_filter.mp hAC).2
    rw [eq_of_inf_ne_bot hB hB' hAB hAB' (π.ne_bot hA)]
  · intro h0
    obtain ⟨B, hB, hfiber⟩ := Finset.mem_image.mp h0
    obtain ⟨A, hA, hAB⟩ := exists_le_of_le hπσ hB
    have hmem : A ∈ blockFiber π B := Finset.mem_filter.mpr ⟨hA, hAB⟩
    rw [hfiber] at hmem
    simpa using hmem

/-- A partition of the block set of `π` induces a coarsening of `π` by taking blockwise unions. -/
private def liftBlockPartition (π : Finpartition a) (Q : Finpartition π.parts) :
    Finpartition a := by
  classical
  refine Finpartition.ofExistsUnique
    (Q.parts.image flattenBlock) ?_ ?_ ?_
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    intro x hx
    obtain ⟨A, hAC, hxA⟩ := Finset.mem_biUnion.mp hx
    exact π.le (Q.le hC hAC) hxA
  · intro x hx
    obtain ⟨A, ⟨hA, hxA⟩, hAuniq⟩ := π.existsUnique_mem hx
    obtain ⟨C, ⟨hC, hAC⟩, hCuniq⟩ := Q.existsUnique_mem hA
    refine ⟨flattenBlock C, ⟨Finset.mem_image.mpr ⟨C, hC, rfl⟩,
      Finset.mem_biUnion.mpr ⟨A, hAC, hxA⟩⟩, ?_⟩
    intro D hD
    obtain ⟨hD, hxD⟩ := hD
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨A', hA'C', hxA'⟩ := Finset.mem_biUnion.mp hxD
    have hA' : A' ∈ π.parts := Q.le hC' hA'C'
    have hAA' : A' = A := hAuniq A' ⟨hA', hxA'⟩
    subst A'
    rw [hCuniq C' ⟨hC', hA'C'⟩]
  · intro h0
    obtain ⟨C, hC, hflatten⟩ := Finset.mem_image.mp h0
    have hC0 : C ≠ ∅ := Q.ne_bot hC
    obtain ⟨A, hAC⟩ := Finset.nonempty_iff_ne_empty.mpr hC0
    have hA : A ∈ π.parts := Q.le hC hAC
    obtain ⟨x, hxA⟩ := Finset.nonempty_iff_ne_empty.mpr (π.ne_bot hA)
    have hx : x ∈ flattenBlock C := Finset.mem_biUnion.mpr ⟨A, hAC, hxA⟩
    rw [hflatten] at hx
    simpa using hx

private theorem flatten_blockFiber_eq {π σ : Finpartition a} (hπσ : π ≤ σ)
    {B : Finset α} (hB : B ∈ σ.parts) :
    flattenBlock (blockFiber π B) = B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hA).2 hxA
  · intro hxB
    have hxa : x ∈ a := σ.le hB hxB
    obtain ⟨A, hA, hxA⟩ := π.exists_mem hxa
    obtain ⟨C, hC, hAC⟩ := hπσ hA
    have hCB : C = B := by
      obtain ⟨D, ⟨hD, hxD⟩, hDuniq⟩ := σ.existsUnique_mem hxa
      exact (hDuniq C ⟨hC, hAC hxA⟩).trans (hDuniq B ⟨hB, hxB⟩).symm
    subst C
    exact Finset.mem_biUnion.mpr
      ⟨A, Finset.mem_filter.mpr ⟨hA, hAC⟩, hxA⟩

private theorem blockFiber_flatten_eq (π : Finpartition a) (Q : Finpartition π.parts)
    {C : Finset (Finset α)} (hC : C ∈ Q.parts) :
    blockFiber π (flattenBlock C) = C := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨hAπ, hAle⟩ := Finset.mem_filter.mp hA
    obtain ⟨x, hxA⟩ := Finset.nonempty_iff_ne_empty.mpr (π.ne_bot hAπ)
    obtain ⟨A', hA'C, hxA'⟩ := Finset.mem_biUnion.mp (hAle hxA)
    have hA'π : A' ∈ π.parts := Q.le hC hA'C
    have hxa : x ∈ a := π.le hAπ hxA
    obtain ⟨D, ⟨hD, hxD⟩, hDuniq⟩ := π.existsUnique_mem hxa
    have hAA' : A = A' :=
      (hDuniq A ⟨hAπ, hxA⟩).trans (hDuniq A' ⟨hA'π, hxA'⟩).symm
    rwa [hAA']
  · intro hAC
    exact Finset.mem_filter.mpr ⟨Q.le hC hAC, fun x hxA =>
      Finset.mem_biUnion.mpr ⟨A, hAC, hxA⟩⟩

private theorem le_liftBlockPartition (π : Finpartition a) (Q : Finpartition π.parts) :
    π ≤ liftBlockPartition π Q := by
  classical
  intro A hA
  obtain ⟨C, hC, hAC⟩ := Q.exists_mem hA
  refine ⟨flattenBlock C, ?_, fun x hxA => Finset.mem_biUnion.mpr ⟨A, hAC, hxA⟩⟩
  exact Finset.mem_image.mpr ⟨C, hC, rfl⟩

private theorem quotientByCoarsening_mono {π σ τ : Finpartition a}
    (hπσ : π ≤ σ) (hπτ : π ≤ τ) (hστ : σ ≤ τ) :
    quotientByCoarsening π σ hπσ ≤ quotientByCoarsening π τ hπτ := by
  classical
  intro C hC
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨D, hD, hBD⟩ := hστ hB
  refine ⟨blockFiber π D, Finset.mem_image.mpr ⟨D, hD, rfl⟩, ?_⟩
  intro A hA
  obtain ⟨hAπ, hAB⟩ := Finset.mem_filter.mp hA
  exact Finset.mem_filter.mpr ⟨hAπ, hAB.trans hBD⟩

private theorem liftBlockPartition_mono (π : Finpartition a) {Q Q' : Finpartition π.parts}
    (hQQ' : Q ≤ Q') : liftBlockPartition π Q ≤ liftBlockPartition π Q' := by
  classical
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨C', hC', hCC'⟩ := hQQ' hC
  refine ⟨flattenBlock C', Finset.mem_image.mpr ⟨C', hC', rfl⟩, ?_⟩
  intro x hx
  obtain ⟨A, hAC, hxA⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨A, hCC' hAC, hxA⟩

private theorem lift_quotientByCoarsening_eq {π σ : Finpartition a} (hπσ : π ≤ σ) :
    liftBlockPartition π (quotientByCoarsening π σ hπσ) = σ := by
  classical
  apply Finpartition.ext
  change (σ.parts.image (blockFiber π)).image flattenBlock = σ.parts
  ext B
  constructor
  · intro hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    simpa [flatten_blockFiber_eq hπσ hD] using hD
  · intro hB
    refine Finset.mem_image.mpr ⟨blockFiber π B,
      Finset.mem_image.mpr ⟨B, hB, rfl⟩, ?_⟩
    exact flatten_blockFiber_eq hπσ hB

private theorem quotient_liftBlockPartition_eq (π : Finpartition a) (Q : Finpartition π.parts) :
    quotientByCoarsening π (liftBlockPartition π Q) (le_liftBlockPartition π Q) = Q := by
  classical
  apply Finpartition.ext
  change (Q.parts.image flattenBlock).image (blockFiber π) = Q.parts
  ext C
  constructor
  · intro hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
    simpa [blockFiber_flatten_eq π Q hD] using hD
  · intro hC
    refine Finset.mem_image.mpr ⟨flattenBlock C,
      Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩
    exact blockFiber_flatten_eq π Q hC

/-- Coarsenings of `π` are equivalent to partitions of the block set of `π`. -/
def coarseningsEquivBlockPartitions (π : Finpartition a) :
    {σ : Finpartition a // π ≤ σ} ≃ Finpartition π.parts where
  toFun σ := quotientByCoarsening π σ.1 σ.2
  invFun Q := ⟨liftBlockPartition π Q, le_liftBlockPartition π Q⟩
  left_inv σ := Subtype.ext (lift_quotientByCoarsening_eq σ.2)
  right_inv Q := quotient_liftBlockPartition_eq π Q

/-- Order-isomorphism form of `coarseningsEquivBlockPartitions`. -/
def coarseningsOrderIsoBlockPartitions (π : Finpartition a) :
    {σ : Finpartition a // π ≤ σ} ≃o Finpartition π.parts where
  toEquiv := coarseningsEquivBlockPartitions π
  map_rel_iff' := by
    intro σ τ
    constructor
    · exact quotientByCoarsening_mono σ.2 τ.2
    · intro h
      change liftBlockPartition π
          (quotientByCoarsening π σ.1 σ.2) ≤
        liftBlockPartition π (quotientByCoarsening π τ.1 τ.2)
      rw [lift_quotientByCoarsening_eq σ.2, lift_quotientByCoarsening_eq τ.2]
      exact liftBlockPartition_mono π h

/-- The Möbius function from a partition to the top depends only on its block set. -/
theorem mu_to_top_eq_mu_bot_top_parts {R : Type*} [CommRing R] (π : Finpartition a) :
    mu R π ⊤ = mu R (⊥ : Finpartition π.parts) ⊤ := by
  classical
  let e := coarseningsOrderIsoBlockPartitions π
  let x : {σ : Finpartition a // π ≤ σ} := ⟨π, le_rfl⟩
  let y : {σ : Finpartition a // π ≤ σ} := ⟨⊤, le_top⟩
  have hex : e x = (⊥ : Finpartition π.parts) := by
    apply le_antisymm
    · have hxy : x ≤ e.symm (⊥ : Finpartition π.parts) := (e.symm ⊥).2
      simpa using e.monotone hxy
    · exact bot_le
  have hey : e y = (⊤ : Finpartition π.parts) := by
    apply le_antisymm
    · exact le_top
    · have hxy : e.symm (⊤ : Finpartition π.parts) ≤ y := le_top
      simpa using e.monotone hxy
  have hiso := IncidenceAlgebra.mu_orderIso_apply (R := R) e x y
  have hambient := IncidenceAlgebra.mu_subtype_ge_apply (R := R) x y
  rw [hex, hey] at hiso
  exact (hiso.trans hambient).symm

end Finpartition
