import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false

/-!
# Finite partitions induced by a sum equivalence

An equivalence `α ⊕ β ≃ γ` partitions the finite target `γ` into the images of its left and right
summands.  This module owns the generic image, cardinality, complement, and subtype-equivalence facts
used by binary and finite-family slot shuffles.
-/

namespace Combinatorics
namespace SumEquiv

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]

/-- Target points occupied by the left summand of an equivalence. -/
def leftImage (e : α ⊕ β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a => e (Sum.inl a))

/-- Target points occupied by the right summand of an equivalence. -/
def rightImage (e : α ⊕ β ≃ γ) : Finset γ :=
  Finset.univ.image (fun b => e (Sum.inr b))

@[simp]
theorem card_leftImage (e : α ⊕ β ≃ γ) :
    (leftImage e).card = Fintype.card α := by
  rw [leftImage, Finset.card_image_of_injective _
    (fun _ _ h => Sum.inl.inj (e.injective h))]
  simp

@[simp]
theorem card_rightImage (e : α ⊕ β ≃ γ) :
    (rightImage e).card = Fintype.card β := by
  rw [rightImage, Finset.card_image_of_injective _
    (fun _ _ h => Sum.inr.inj (e.injective h))]
  simp

@[simp]
theorem mem_leftImage_iff (e : α ⊕ β ≃ γ) (x : γ) :
    x ∈ leftImage e ↔ ∃ a : α, e (Sum.inl a) = x := by
  simp [leftImage]

@[simp]
theorem mem_rightImage_iff (e : α ⊕ β ≃ γ) (x : γ) :
    x ∈ rightImage e ↔ ∃ b : β, e (Sum.inr b) = x := by
  simp [rightImage]

/-- The right image is exactly the complement of the left image. -/
theorem mem_rightImage_iff_not_mem_leftImage (e : α ⊕ β ≃ γ) (x : γ) :
    x ∈ rightImage e ↔ x ∉ leftImage e := by
  constructor
  · intro hright hleft
    obtain ⟨b, hb⟩ := (mem_rightImage_iff e x).1 hright
    obtain ⟨a, ha⟩ := (mem_leftImage_iff e x).1 hleft
    have htag : (Sum.inr b : α ⊕ β) = Sum.inl a :=
      e.injective (hb.trans ha.symm)
    cases htag
  · intro hleft
    cases hpre : e.symm x with
    | inl a =>
        exfalso
        apply hleft
        exact (mem_leftImage_iff e x).2 ⟨a, by
          have h := e.apply_symm_apply x
          rw [hpre] at h
          exact h⟩
    | inr b =>
        exact (mem_rightImage_iff e x).2 ⟨b, by
          have h := e.apply_symm_apply x
          rw [hpre] at h
          exact h⟩

/-- Finset form of the right-image/complement identity. -/
theorem rightImage_eq_sdiff_leftImage (e : α ⊕ β ≃ γ) :
    rightImage e = (Finset.univ : Finset γ) \ leftImage e := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact mem_rightImage_iff_not_mem_leftImage e x

/-- The left summand is equivalent to the subtype of target points in its image. -/
noncomputable def leftSubtypeEquiv (e : α ⊕ β ≃ γ) :
    α ≃ ↥(leftImage e) :=
  (Equiv.ofInjective (fun a : α => e (Sum.inl a))
      (fun _ _ h => Sum.inl.inj (e.injective h))).trans
    (Equiv.setCongr (by
      ext x
      simp [leftImage]))

/-- The right summand is equivalent to the subtype of target points in its image. -/
noncomputable def rightSubtypeEquiv (e : α ⊕ β ≃ γ) :
    β ≃ ↥(rightImage e) :=
  (Equiv.ofInjective (fun b : β => e (Sum.inr b))
      (fun _ _ h => Sum.inr.inj (e.injective h))).trans
    (Equiv.setCongr (by
      ext x
      simp [rightImage]))

@[simp]
theorem leftSubtypeEquiv_val (e : α ⊕ β ≃ γ) (a : α) :
    ((leftSubtypeEquiv e a : ↥(leftImage e)) : γ) = e (Sum.inl a) := by
  rfl

@[simp]
theorem rightSubtypeEquiv_val (e : α ⊕ β ≃ γ) (b : β) :
    ((rightSubtypeEquiv e b : ↥(rightImage e)) : γ) = e (Sum.inr b) := by
  rfl

end SumEquiv
end Combinatorics
