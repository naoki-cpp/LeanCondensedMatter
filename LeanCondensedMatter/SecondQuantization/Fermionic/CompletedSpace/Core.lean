import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators

set_option linter.style.header false

/-!
# Algebraic core of completed fermionic ladder operators

This file identifies the bounded completed creation and annihilation operators with the existing
algebraic operators under the canonical dense inclusion into completed Fock space. Their occupation-
basis action is proved alongside the structural operator construction in `Operators.lean`.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}
variable [LinearOrder Mode]

/-- Completed creation agrees with algebraic creation on every finite-support vector. -/
theorem completedCreate_comp_algebraicToCompleted (i : Mode) :
    (completedCreate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (create i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedCreate i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (create i (basisState n))
  rw [show algebraicToCompleted (basisState n) = completedBasisState n by
    simpa [algebraicToCompleted, basisState, completedBasisState] using
      (Common.algebraicToCompleted_basisState (Config := Occupation Mode) n)]
  by_cases hi : i ∈ n
  · simp [create_basisState_of_mem hi, completedCreate_basisState_of_mem hi]
  · simp [create_basisState_of_not_mem hi, completedCreate_basisState_of_not_mem hi,
      fermionPhase]

/-- Completed annihilation agrees with algebraic annihilation on every finite-support vector. -/
theorem completedAnnihilate_comp_algebraicToCompleted (i : Mode) :
    (completedAnnihilate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (annihilate i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedAnnihilate i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (annihilate i (basisState n))
  rw [show algebraicToCompleted (basisState n) = completedBasisState n by
    simpa [algebraicToCompleted, basisState, completedBasisState] using
      (Common.algebraicToCompleted_basisState (Config := Occupation Mode) n)]
  by_cases hi : i ∈ n
  · simp [annihilate_basisState_of_mem hi, completedAnnihilate_basisState_of_mem hi,
      fermionPhase]
  · simp [annihilate_basisState_of_not_mem hi, completedAnnihilate_basisState_of_not_mem hi]

end
end Fermionic
end SecondQuantization
