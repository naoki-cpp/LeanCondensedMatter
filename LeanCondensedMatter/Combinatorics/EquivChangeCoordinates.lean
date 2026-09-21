import Mathlib.Logic.Equiv.Basic

set_option linter.style.header false

/-!
# Coordinate changes between equivalences

Two equivalences with the same source determine a canonical equivalence between their targets.
This module packages the common change-of-coordinates construction
`source.symm.trans target` and its basic composition laws.
-/

namespace Equiv

/-- The coordinate change from the target of `source` to the target of `target`, when both
coordinate systems parametrize the same source type. -/
def changeCoordinates {α β γ : Type*} (source : α ≃ β) (target : α ≃ γ) : β ≃ γ :=
  source.symm.trans target

/-- Evaluate a coordinate change at an arbitrary point in the source coordinate space. -/
@[simp]
theorem changeCoordinates_apply {α β γ : Type*}
    (source : α ≃ β) (target : α ≃ γ) (y : β) :
    source.changeCoordinates target y = target (source.symm y) := by
  rfl

/-- Changing coordinates sends the `source` representation of an element to its `target`
representation. -/
@[simp]
theorem changeCoordinates_apply_source {α β γ : Type*}
    (source : α ≃ β) (target : α ≃ γ) (x : α) :
    source.changeCoordinates target (source x) = target x := by
  simp [Equiv.changeCoordinates]

/-- A coordinate system differs from itself by the identity equivalence. -/
@[simp]
theorem changeCoordinates_self {α β : Type*} (e : α ≃ β) :
    e.changeCoordinates e = Equiv.refl β := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp

/-- Reversing a coordinate change swaps its source and target systems. -/
@[simp]
theorem changeCoordinates_symm {α β γ : Type*} (source : α ≃ β) (target : α ≃ γ) :
    (source.changeCoordinates target).symm = target.changeCoordinates source := by
  ext x
  obtain ⟨y, rfl⟩ := target.surjective x
  simp [Equiv.changeCoordinates]

/-- Coordinate changes compose through an intermediate representation. -/
theorem changeCoordinates_trans {α β γ δ : Type*}
    (first : α ≃ β) (middle : α ≃ γ) (last : α ≃ δ) :
    (first.changeCoordinates middle).trans (middle.changeCoordinates last) =
      first.changeCoordinates last := by
  ext x
  obtain ⟨y, rfl⟩ := first.surjective x
  simp

end Equiv
