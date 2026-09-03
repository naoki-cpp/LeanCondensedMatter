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

variable {Mode : Type*}
variable [LinearOrder Mode]

@[simp]
theorem completedCreate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedCreate i (completedBasisState n) = 0 := by
  classical
  ext m
  by_cases hm : i ∈ m
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      have hnot : i ∉ toggleOccupation i m := by
        intro ht
        exact ((mem_toggleOccupation i m).mp ht) hm
      apply hnot
      simpa [h] using hi
    rw [completedCreate_apply, if_pos hm]
    rw [completedBasisState_apply_of_ne htoggle]
    simp
  · rw [completedCreate_apply, if_neg hm]
    simp

@[simp]
theorem completedCreate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedCreate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (insertOccupation i n) := by
  classical
  ext m
  rw [completedCreate_apply]
  change (if i ∈ m then fermionPhase i (toggleOccupation i m) *
      completedBasisState n (toggleOccupation i m) else 0) =
    fermionPhase i n * completedBasisState (insertOccupation i n) m
  by_cases hm : m = insertOccupation i n
  · subst m
    have him : i ∈ insertOccupation i n := by
      simp [insertOccupation]
    have ht : toggleOccupation i (insertOccupation i n) = n := by
      rw [← toggleOccupation_of_not_mem hi]
      exact toggleOccupation_involutive i n
    rw [if_pos him, ht, completedBasisState_apply_self, completedBasisState_apply_self]
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      apply hm
      calc
        m = toggleOccupation i (toggleOccupation i m) :=
          (toggleOccupation_involutive i m).symm
        _ = toggleOccupation i n := congrArg (toggleOccupation i) h
        _ = insertOccupation i n := toggleOccupation_of_not_mem hi
    by_cases him : i ∈ m
    · rw [if_pos him, completedBasisState_apply_of_ne htoggle,
        completedBasisState_apply_of_ne hm]
      simp
    · rw [if_neg him, completedBasisState_apply_of_ne hm]
      simp

@[simp]
theorem completedAnnihilate_basisState_of_not_mem {i : Mode} {n : Occupation Mode} (hi : i ∉ n) :
    completedAnnihilate i (completedBasisState n) = 0 := by
  classical
  ext m
  by_cases hm : i ∈ m
  · rw [completedAnnihilate_apply, if_pos hm]
    simp
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      have hmem : i ∈ toggleOccupation i m :=
        (mem_toggleOccupation i m).mpr hm
      apply hi
      simpa [h] using hmem
    rw [completedAnnihilate_apply, if_neg hm]
    rw [completedBasisState_apply_of_ne htoggle]
    simp

@[simp]
theorem completedAnnihilate_basisState_of_mem {i : Mode} {n : Occupation Mode} (hi : i ∈ n) :
    completedAnnihilate i (completedBasisState n) =
      fermionPhase i n • completedBasisState (removeOccupation i n) := by
  classical
  ext m
  rw [completedAnnihilate_apply]
  change (if i ∈ m then 0 else fermionPhase i (toggleOccupation i m) *
      completedBasisState n (toggleOccupation i m)) =
    fermionPhase i n * completedBasisState (removeOccupation i n) m
  by_cases hm : m = removeOccupation i n
  · subst m
    have him : i ∉ removeOccupation i n := by
      simp [removeOccupation]
    have ht : toggleOccupation i (removeOccupation i n) = n := by
      rw [← toggleOccupation_of_mem hi]
      exact toggleOccupation_involutive i n
    rw [if_neg him, ht, completedBasisState_apply_self, completedBasisState_apply_self]
  · have htoggle : toggleOccupation i m ≠ n := by
      intro h
      apply hm
      calc
        m = toggleOccupation i (toggleOccupation i m) :=
          (toggleOccupation_involutive i m).symm
        _ = toggleOccupation i n := congrArg (toggleOccupation i) h
        _ = removeOccupation i n := toggleOccupation_of_mem hi
    by_cases him : i ∈ m
    · rw [if_pos him, completedBasisState_apply_of_ne hm]
      simp
    · rw [if_neg him, completedBasisState_apply_of_ne htoggle,
        completedBasisState_apply_of_ne hm]
      simp

/-- Completed creation agrees with algebraic creation on every finite-support vector. -/
theorem completedCreate_comp_algebraicToCompleted (i : Mode) :
    (completedCreate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (create i) := by
  apply Finsupp.lhom_ext
  intro n c
  have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
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
  have hc : (Finsupp.single n c : OccupationFock Mode) = c • basisState n :=
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
