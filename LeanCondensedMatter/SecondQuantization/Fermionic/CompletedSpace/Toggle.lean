import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation

set_option linter.style.header false

/-!
# Occupation toggling for completed fermionic CAR operators

Completed fermionic creation and annihilation operators are signed partial reindexings of the
occupation basis. Their common reindexing map toggles one mode: occupied configurations are sent to
the corresponding unoccupied configuration and conversely.

This file isolates that combinatorial equivalence before constructing the bounded `ℓ²` operators.
Keeping the reindexing separate makes the later norm proof a statement about an isometric basis
permutation followed by an occupation projection.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- Toggle the occupation of one fermionic mode. -/
def toggleOccupation (i : Mode) (n : Occupation Mode) : Occupation Mode :=
  if i ∈ n then removeOccupation i n else insertOccupation i n

@[simp]
theorem mem_toggleOccupation (i : Mode) (n : Occupation Mode) :
    i ∈ toggleOccupation i n ↔ i ∉ n := by
  by_cases h : i ∈ n
  · simp [toggleOccupation, h, removeOccupation]
  · simp [toggleOccupation, h, insertOccupation]

@[simp]
theorem toggleOccupation_of_mem {i : Mode} {n : Occupation Mode} (h : i ∈ n) :
    toggleOccupation i n = removeOccupation i n := by
  simp [toggleOccupation, h]

@[simp]
theorem toggleOccupation_of_not_mem {i : Mode} {n : Occupation Mode} (h : i ∉ n) :
    toggleOccupation i n = insertOccupation i n := by
  simp [toggleOccupation, h]

@[simp]
theorem toggleOccupation_involutive (i : Mode) :
    Function.Involutive (toggleOccupation i) := by
  intro n
  by_cases h : i ∈ n
  · simp [toggleOccupation, h, removeOccupation, insertOccupation]
  · simp [toggleOccupation, h, removeOccupation, insertOccupation]

/-- Toggling one mode is an equivalence of the full occupation basis. -/
def toggleOccupationEquiv (i : Mode) : Occupation Mode ≃ Occupation Mode where
  toFun := toggleOccupation i
  invFun := toggleOccupation i
  left_inv := toggleOccupation_involutive i
  right_inv := toggleOccupation_involutive i

@[simp]
theorem toggleOccupationEquiv_apply (i : Mode) (n : Occupation Mode) :
    toggleOccupationEquiv i n = toggleOccupation i n :=
  rfl

@[simp]
theorem toggleOccupationEquiv_symm (i : Mode) :
    (toggleOccupationEquiv i).symm = toggleOccupationEquiv i :=
  rfl

/-- The fermionic sign, regarded as a complex phase for completed-space operators. -/
def fermionPhase (i : Mode) (n : Occupation Mode) : ℂ :=
  fermionSign i n

@[simp]
theorem norm_fermionPhase (i : Mode) (n : Occupation Mode) :
    ‖fermionPhase i n‖ = 1 := by
  simp [fermionPhase, fermionSign]

end Fermionic
end SecondQuantization
