import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder

set_option linter.style.header false

/-!
# Statistics-independent interaction-slot relabeling for two-point legs

A permutation of interaction slots fixes the two external legs and relabels each interaction leg
without changing its local quartic coordinate. This is purely structural and is shared by any
statistics-specific two-point diagram realization.
-/

namespace SecondQuantization
namespace Common

noncomputable section

/-- Relabel the standard two-point leg type by an interaction-slot permutation, leaving the two
external legs fixed. The permutation maps new leg identities to old leg identities. -/
def interactionVertexLegRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    OrderedTwoPointLeg n ≃ OrderedTwoPointLeg n where
  toFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π p.1.1, Finset.mem_univ _⟩, p.2)
  invFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π.symm p.1.1, Finset.mem_univ _⟩, p.2)
  left_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp
  right_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp

@[simp]
theorem interactionVertexLegRelabel_external {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin 2) :
    interactionVertexLegRelabel π (Sum.inl e) = (Sum.inl e : OrderedTwoPointLeg n) :=
  rfl

@[simp]
theorem interactionVertexLegRelabel_interaction {n : ℕ} (π : Equiv.Perm (Fin n))
    (v : Fin n) (l : Fin 4) :
    interactionVertexLegRelabel π
        (Sum.inr (⟨v, Finset.mem_univ v⟩, l)) =
      (Sum.inr (⟨π v, Finset.mem_univ (π v)⟩, l) : OrderedTwoPointLeg n) :=
  rfl

/-- The flattened standard-leg permutation induced by an interaction-slot permutation. -/
def interactionVertexPositionRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :=
  (twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
    ((interactionVertexLegRelabel π).trans
      (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm)

/-- Relabeling standard two-point legs by the inverse slot permutation is the inverse leg
relabeling. -/
@[simp]
theorem interactionVertexLegRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexLegRelabel π.symm = (interactionVertexLegRelabel π).symm := by
  ext leg
  rcases leg with e | ⟨v, l⟩
  · rfl
  · rfl

/-- The flattened position relabeling induced by the inverse slot permutation is the inverse
flattened position relabeling. -/
@[simp]
theorem interactionVertexPositionRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexPositionRelabel π.symm =
      (interactionVertexPositionRelabel π).symm := by
  unfold interactionVertexPositionRelabel
  rw [interactionVertexLegRelabel_symm]
  rfl

end

end Common
end SecondQuantization
