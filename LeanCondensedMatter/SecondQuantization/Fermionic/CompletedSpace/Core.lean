import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator

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
  have hbasis (m : Occupation Mode) :
      algebraicToCompleted (basisState m) = completedBasisState m := by
    simpa [algebraicToCompleted, basisState, completedBasisState] using
      (Common.algebraicToCompleted_basisState (Config := Occupation Mode) m)
  rw [hbasis n]
  by_cases hi : i ∈ n
  · simp [create_basisState_of_mem hi, completedCreate_basisState_of_mem hi]
  · simp [create_basisState_of_not_mem hi, completedCreate_basisState_of_not_mem hi,
      fermionPhase, hbasis]


/-- The completed single-mode number operator agrees with the algebraic number operator on every
finite-support vector. -/
theorem completedNumberOperator_comp_algebraicToCompleted (i : Mode) :
    (completedNumberOperator i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (numberOperator i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedNumberOperator i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (numberOperator i (basisState n))
  have hbasis (m : Occupation Mode) :
      algebraicToCompleted (basisState m) = completedBasisState m := by
    simpa [algebraicToCompleted, basisState, completedBasisState] using
      (Common.algebraicToCompleted_basisState (Config := Occupation Mode) m)
  rw [hbasis n, completedNumberOperator_basisState, numberOperator_basisState]
  by_cases hi : i ∈ n
  · simp [hi, hbasis]
  · simp [hi]

/-- The completed single-mode number operator is the completed product `aᵢ† aᵢ`. -/
theorem completedNumberOperator_eq_create_comp_annihilate (i : Mode) :
    completedNumberOperator i = (completedCreate i).comp (completedAnnihilate i) := by
  apply Common.continuousLinearMap_ext_algebraicCore
  intro x
  have hN := DFunLike.congr_fun (completedNumberOperator_comp_algebraicToCompleted i) x
  have ha := DFunLike.congr_fun (completedAnnihilate_comp_algebraicToCompleted i) x
  have hc := DFunLike.congr_fun (completedCreate_comp_algebraicToCompleted i) (annihilate i x)
  simp only [LinearMap.comp_apply] at hN ha hc
  rw [hN, ContinuousLinearMap.comp_apply, ha, hc]
  rfl

/-- Completed annihilation agrees with algebraic annihilation on every finite-support vector. -/
theorem completedAnnihilate_comp_algebraicToCompleted (i : Mode) :
    (completedAnnihilate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (annihilate i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedAnnihilate i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (annihilate i (basisState n))
  have hbasis (m : Occupation Mode) :
      algebraicToCompleted (basisState m) = completedBasisState m := by
    simpa [algebraicToCompleted, basisState, completedBasisState] using
      (Common.algebraicToCompleted_basisState (Config := Occupation Mode) m)
  rw [hbasis n]
  by_cases hi : i ∈ n
  · simp [annihilate_basisState_of_mem hi, completedAnnihilate_basisState_of_mem hi,
      fermionPhase, hbasis]
  · simp [annihilate_basisState_of_not_mem hi, completedAnnihilate_basisState_of_not_mem hi]

end
end Fermionic
end SecondQuantization
