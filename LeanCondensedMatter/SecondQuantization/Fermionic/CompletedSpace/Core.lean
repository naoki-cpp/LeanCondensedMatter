import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators

set_option linter.style.header false

/-!
# Algebraic core of completed fermionic ladder operators

This file proves the occupation-basis action of the bounded completed creation and annihilation
operators and identifies them with the existing algebraic operators under the canonical dense
inclusion into completed Fock space.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

@[simp]
theorem completedCreate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedCreate i (completedBasisState n) = 0 := by
  classical
  apply lp.ext
  funext m
  by_cases hm : i ∈ m
  · have hne : toggleOccupation i m ≠ n := by
      intro h
      have : i ∉ n := by
        rw [← h]
        exact (mem_toggleOccupation i m).mp rfl
      exact this hi
    simp [completedCreate_apply, completedBasisState, hm, hne, lp.single_apply]
  · simp [completedCreate_apply, hm]

@[simp]
theorem completedCreate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedCreate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (insertOccupation i n) := by
  classical
  apply lp.ext
  funext m
  by_cases hm : m = insertOccupation i n
  · subst m
    simp [completedCreate_apply, completedBasisState, hi, lp.single_apply,
      toggleOccupation_of_mem, insertOccupation]
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      apply hm
      calc
        m = toggleOccupation i (toggleOccupation i m) :=
          (toggleOccupation_involutive i m).symm
        _ = toggleOccupation i n := congrArg (toggleOccupation i) h
        _ = insertOccupation i n := toggleOccupation_of_not_mem hi
    by_cases him : i ∈ m
    · simp [completedCreate_apply, completedBasisState, him, hm, htoggle, lp.single_apply]
    · simp [completedCreate_apply, him, completedBasisState, hm, lp.single_apply]

@[simp]
theorem completedAnnihilate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedAnnihilate i (completedBasisState n) = 0 := by
  classical
  apply lp.ext
  funext m
  by_cases hm : i ∈ m
  · simp [completedAnnihilate_apply, hm]
  · have hne : toggleOccupation i m ≠ n := by
      intro h
      have : i ∈ n := by
        rw [← h]
        exact (mem_toggleOccupation i m).mpr hm
      exact hi this
    simp [completedAnnihilate_apply, completedBasisState, hm, hne, lp.single_apply]

@[simp]
theorem completedAnnihilate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedAnnihilate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (removeOccupation i n) := by
  classical
  apply lp.ext
  funext m
  by_cases hm : m = removeOccupation i n
  · subst m
    simp [completedAnnihilate_apply, completedBasisState, hi, lp.single_apply,
      toggleOccupation_of_not_mem, removeOccupation]
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      apply hm
      calc
        m = toggleOccupation i (toggleOccupation i m) :=
          (toggleOccupation_involutive i m).symm
        _ = toggleOccupation i n := congrArg (toggleOccupation i) h
        _ = removeOccupation i n := toggleOccupation_of_mem hi
    by_cases him : i ∈ m
    · simp [completedAnnihilate_apply, him]
    · simp [completedAnnihilate_apply, completedBasisState, him, hm, htoggle, lp.single_apply]

/-- Completed creation agrees with algebraic creation on every finite-support vector. -/
theorem completedCreate_comp_algebraicToCompleted (i : Mode) :
    (completedCreate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (create i) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : FockSpace Mode) = c • basisState n :=
    (Finsupp.smul_single_one n c).symm
  rw [hc]
  simp only [LinearMap.comp_apply, map_smul, algebraicToCompleted_basisState]
  by_cases hi : i ∈ n
  · simp [create_basisState_of_mem hi, completedCreate_basisState_of_mem hi]
  · simp [create_basisState_of_not_mem hi, completedCreate_basisState_of_not_mem hi,
      fermionPhase]

/-- Completed annihilation agrees with algebraic annihilation on every finite-support vector. -/
theorem completedAnnihilate_comp_algebraicToCompleted (i : Mode) :
    (completedAnnihilate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (annihilate i) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : FockSpace Mode) = c • basisState n :=
    (Finsupp.smul_single_one n c).symm
  rw [hc]
  simp only [LinearMap.comp_apply, map_smul, algebraicToCompleted_basisState]
  by_cases hi : i ∈ n
  · simp [annihilate_basisState_of_mem hi, completedAnnihilate_basisState_of_mem hi,
      fermionPhase]
  · simp [annihilate_basisState_of_not_mem hi, completedAnnihilate_basisState_of_not_mem hi]

end
end Fermionic
end SecondQuantization
