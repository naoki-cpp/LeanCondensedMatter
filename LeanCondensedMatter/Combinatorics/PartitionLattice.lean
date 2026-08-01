import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import LeanCondensedMatter.Combinatorics.IncidenceAlgebraMu

set_option linter.style.header false

/-!
# The partition lattice and its Möbius function

This module supplies the refinement-fiber decomposition of `Finpartition` and factors the Möbius
function over the blocks of a coarser partition.  The coefficient ring is arbitrary.
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α] {s : Finset α}

noncomputable instance instLocallyFiniteOrder : LocallyFiniteOrder (Finpartition s) := by
  classical
  exact Fintype.toLocallyFiniteOrder

namespace Finpartition

variable {a : Finset α}

/-- A partition obtained by independently refining every block refines the original partition. -/
theorem bind_le (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : P.bind Q ≤ P := by
  intro d hd
  obtain ⟨A, hA, hdA⟩ := mem_bind.1 hd
  exact ⟨A, hA, (Q A hA).le hdA⟩

/-- Membership in a restricted partition. -/
theorem mem_restrict_iff {P : Finpartition a} {hb : b ≤ a} {d : Finset α} :
    d ∈ (P.restrict hb).parts ↔ d ≠ ⊥ ∧ ∃ A ∈ P.parts, A ⊓ b = d := by
  simp only [restrict, Finset.mem_erase, Finset.mem_image]

/-- Two blocks containing the same nonempty finite set coincide. -/
theorem eq_of_inf_ne_bot {σ : Finpartition a} {A B B' : Finset α} (hB : B ∈ σ.parts)
    (hB' : B' ∈ σ.parts) (hAB : A ≤ B) (hAB' : A ≤ B') (hA : A ≠ ⊥) : B = B' := by
  by_contra hne
  have hdisj : Disjoint B B' := σ.disjoint hB hB' hne
  have hle : A ≤ B ⊓ B' := le_inf hAB hAB'
  rw [hdisj.eq_bot] at hle
  exact hA (bot_unique hle)

/-- Restricting a refinement to every block and binding the results recovers the refinement. -/
theorem bind_restrict_eq_of_le {σ π : Finpartition a} (h : π ≤ σ) :
    σ.bind (fun _B hB => π.restrict (σ.le hB)) = π := by
  ext d
  rw [mem_bind]
  constructor
  · rintro ⟨B, hB, hd⟩
    rw [mem_restrict_iff] at hd
    obtain ⟨hd0, A, hA, rfl⟩ := hd
    obtain ⟨B', hB', hAB'⟩ := h hA
    have hBB' : B = B' := eq_of_inf_ne_bot hB hB' inf_le_right (inf_le_left.trans hAB') hd0
    rwa [hBB', inf_eq_left.2 hAB']
  · intro hd
    obtain ⟨B, hB, hdB⟩ := h hd
    refine ⟨B, hB, ?_⟩
    rw [mem_restrict_iff]
    exact ⟨π.ne_bot hd, d, hd, inf_eq_left.2 hdB⟩

/-- Binding blockwise partitions and restricting to one original block recovers that partition. -/
theorem restrict_bind_eq (σ : Finpartition a) (Q : ∀ B ∈ σ.parts, Finpartition B) {B : Finset α}
    (hB : B ∈ σ.parts) : (σ.bind Q).restrict (σ.le hB) = Q B hB := by
  ext d
  rw [mem_restrict_iff]
  constructor
  · rintro ⟨hd0, A, hA, rfl⟩
    obtain ⟨C, hC, hAC⟩ := mem_bind.1 hA
    have hAleC : A ≤ C := (Q C hC).le hAC
    have hCB : C = B := eq_of_inf_ne_bot hC hB (inf_le_left.trans hAleC) inf_le_right hd0
    subst hCB
    rwa [inf_eq_left.2 hAleC]
  · intro hd
    exact ⟨(Q B hB).ne_bot hd, d, mem_bind.2 ⟨B, hB, hd⟩,
      inf_eq_left.2 ((Q B hB).le hd)⟩

/-- Restriction is monotone with respect to refinement. -/
theorem restrict_mono {P P' : Finpartition a} (h : P ≤ P') {b : Finset α} (hb : b ≤ a) :
    P.restrict hb ≤ P'.restrict hb := by
  intro d hd
  rw [mem_restrict_iff] at hd
  obtain ⟨hd0, A, hA, rfl⟩ := hd
  obtain ⟨C, hC, hAC⟩ := h hA
  refine ⟨C ⊓ b, ?_, inf_le_inf_right b hAC⟩
  rw [mem_restrict_iff]
  exact ⟨ne_bot_of_le_ne_bot hd0 (inf_le_inf_right b hAC), C, hC, rfl⟩

/-- Refinements of `σ` are independent choices of a partition on every block of `σ`. -/
def refinementsEquivFiberPartitions (σ : Finpartition a) :
    {π : Finpartition a // π ≤ σ} ≃ (∀ B : σ.parts, Finpartition (B : Finset α)) where
  toFun π B := π.1.restrict (σ.le B.2)
  invFun Q := ⟨σ.bind (fun B hB => Q ⟨B, hB⟩), bind_le σ _⟩
  left_inv π := Subtype.ext (bind_restrict_eq_of_le π.2)
  right_inv Q := funext fun B => restrict_bind_eq σ (fun C hC => Q ⟨C, hC⟩) B.2

/-- Order-isomorphism form of `refinementsEquivFiberPartitions`. -/
def refinementsOrderIsoFiberPartitions (σ : Finpartition a) :
    {π : Finpartition a // π ≤ σ} ≃o (∀ B : σ.parts, Finpartition (B : Finset α)) where
  toEquiv := refinementsEquivFiberPartitions σ
  map_rel_iff' := by
    intro π π'
    refine ⟨fun h A hA => ?_, fun h B => restrict_mono h (σ.le B.2)⟩
    obtain ⟨B, hB, hAB⟩ := π.2 hA
    have hAmem : A ∈ (π.1.restrict (σ.le hB)).parts := by
      rw [mem_restrict_iff]
      exact ⟨π.1.ne_bot hA, A, hA, inf_eq_left.2 hAB⟩
    obtain ⟨D, hD, hAD⟩ := h ⟨B, hB⟩ hAmem
    have hD' : D ∈ (π'.1.restrict (σ.le hB)).parts := hD
    rw [mem_restrict_iff] at hD'
    obtain ⟨-, C, hC, rfl⟩ := hD'
    exact ⟨C, hC, hAD.trans inf_le_left⟩

/-- A partition restricted to one of its own blocks is the indiscrete partition of that block. -/
theorem restrict_self_part_eq_top (σ : Finpartition a) {B : Finset α} (hB : B ∈ σ.parts) :
    σ.restrict (σ.le hB) = (⊤ : Finpartition B) := by
  classical
  have hparts : (σ.restrict (σ.le hB)).parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨mem_restrict_iff.2 ⟨σ.ne_bot hB, B, hB, inf_idem B⟩, fun d hd => ?_⟩
    rw [mem_restrict_iff] at hd
    obtain ⟨hd0, C, hC, rfl⟩ := hd
    by_contra hne
    exact hd0 (bot_unique (σ.disjoint hC hB (fun h => hne (h ▸ inf_idem B))).le_bot)
  have htop : (⊤ : Finpartition B).parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, fun d hd => Finset.mem_singleton.1 (Finpartition.parts_top_subset B hd)⟩
    obtain ⟨x, hx⟩ := (Finpartition.parts_nonempty_iff (P := (⊤ : Finpartition B))).2
      (σ.ne_bot hB)
    rwa [Finset.mem_singleton.1 (Finpartition.parts_top_subset B hx)] at hx
  exact Finpartition.ext (hparts.trans htop.symm)

/-- The partition-lattice Möbius function factors over the blocks of the coarser partition. -/
theorem mu_eq_prod_restrict {R : Type*} [CommRing R]
    {π σ : Finpartition a} (h : π ≤ σ) :
    mu R π σ = ∏ B : σ.parts, mu R (π.restrict (σ.le B.2))
      (⊤ : Finpartition (B : Finset α)) := by
  classical
  have hstep1 : mu R π σ =
      mu R (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ :=
    (mu_subtype_le_apply (R := R)
      (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩).symm
  have hstep2 :
      mu R (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ =
        mu R (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
          (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩) :=
    (mu_orderIso_apply (R := R) _ _ _).symm
  have hstep3 := mu_pi_finset_apply (R := R)
    (fun B : Finset α => Finpartition B) σ.parts
    (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
    (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩)
  rw [hstep1, hstep2, hstep3]
  refine Finset.prod_congr rfl fun B _ => ?_
  change mu R (π.restrict (σ.le B.2)) (σ.restrict (σ.le B.2)) =
    mu R (π.restrict (σ.le B.2)) ⊤
  rw [restrict_self_part_eq_top σ B.2]

end Finpartition
