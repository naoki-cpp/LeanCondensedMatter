import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import Mathlib.Analysis.InnerProductSpace.Adjoint

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

private theorem algebraicToCompleted_basisState' (n : Occupation Mode) :
    algebraicToCompleted (basisState n) = completedBasisState n := by
  simpa [algebraicToCompleted, basisState, completedBasisState] using
    (Common.algebraicToCompleted_basisState (Config := Occupation Mode) n)

/-- Completed creation agrees with algebraic creation on every finite-support vector. -/
theorem completedCreate_comp_algebraicToCompleted (i : Mode) :
    (completedCreate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (create i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedCreate i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (create i (basisState n))
  rw [algebraicToCompleted_basisState' n]
  by_cases hi : i ∈ n
  · simp [create_basisState_of_mem hi, completedCreate_basisState_of_mem hi]
  · simp [create_basisState_of_not_mem hi, completedCreate_basisState_of_not_mem hi,
      fermionPhase, algebraicToCompleted_basisState']

/-- Completed annihilation agrees with algebraic annihilation on every finite-support vector. -/
theorem completedAnnihilate_comp_algebraicToCompleted (i : Mode) :
    (completedAnnihilate i).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp (annihilate i) := by
  apply Common.linearMap_ext_basisState
  intro n
  change completedAnnihilate i (algebraicToCompleted (basisState n)) =
    algebraicToCompleted (annihilate i (basisState n))
  rw [algebraicToCompleted_basisState' n]
  by_cases hi : i ∈ n
  · simp [annihilate_basisState_of_mem hi, completedAnnihilate_basisState_of_mem hi,
      fermionPhase, algebraicToCompleted_basisState']
  · simp [annihilate_basisState_of_not_mem hi, completedAnnihilate_basisState_of_not_mem hi]

/-- Completed creation and annihilation are Hilbert adjoints for arbitrary mode types. -/
@[simp]
theorem star_completedCreate (i : Mode) : star (completedCreate i) = completedAnnihilate i := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  ext m
  change (star (completedCreate i) (completedBasisState n)) m =
    (completedAnnihilate i (completedBasisState n)) m
  rw [← inner_completedBasisState_left, ← inner_completedBasisState_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm]
  have hcore (T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
      (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
      (h : T.toLinearMap.comp algebraicToCompleted = algebraicToCompleted.comp A)
      (p q : Occupation Mode) :
      inner ℂ (completedBasisState p) (T (completedBasisState q)) =
        Common.matrixCoeff A p q := by
    have hq := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode =>
      f (basisState q)) h
    have hb : algebraicToCompleted (basisState q) = completedBasisState q := by
      exact Common.algebraicToCompleted_basisState q
    simp only [LinearMap.comp_apply, hb] at hq
    change T (completedBasisState q) = algebraicToCompleted (A (basisState q)) at hq
    rw [hq, inner_completedBasisState_left]
    rfl
  rw [hcore _ _ (completedCreate_comp_algebraicToCompleted i),
    hcore _ _ (completedAnnihilate_comp_algebraicToCompleted i)]
  exact star_matrixCoeff_create_eq_matrixCoeff_annihilate i m n

end
end Fermionic
end SecondQuantization
