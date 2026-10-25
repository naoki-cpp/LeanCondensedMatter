import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Canonical anticommutation relations on completed fermionic Fock space

The completed creation and annihilation operators are bounded continuous linear maps. This file
lifts the algebraic canonical anticommutation relations to the `ℓ²` completion. Rather than repeat
the occupation-coordinate sign calculation, the proof uses agreement with the algebraic ladder
operators on the finite-support core together with density of that core and continuity.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private theorem completedCreate_algebraicToCompleted (i : Mode) (x : OccupationFock Mode) :
    completedCreate i (Common.algebraicToCompleted x) =
      Common.algebraicToCompleted (create i x) := by
  change (completedCreate i).toLinearMap (algebraicToCompleted x) =
    algebraicToCompleted (create i x)
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedCreate_comp_algebraicToCompleted i)

private theorem completedAnnihilate_algebraicToCompleted (i : Mode) (x : OccupationFock Mode) :
    completedAnnihilate i (Common.algebraicToCompleted x) =
      Common.algebraicToCompleted (annihilate i x) := by
  change (completedAnnihilate i).toLinearMap (algebraicToCompleted x) =
    algebraicToCompleted (annihilate i x)
  simpa only [LinearMap.comp_apply] using
    congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedAnnihilate_comp_algebraicToCompleted i)

/-- Completed creation operators anticommute. -/
theorem completedAnticomm_create_create (i j : Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (completedCreate i) (completedCreate j) = 0 := by
  apply Common.continuousLinearMap_ext_algebraicCore
  intro x
  simp only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add, add_apply,
    mul_apply_eq_comp]
  rw [completedCreate_algebraicToCompleted j x,
    completedCreate_algebraicToCompleted i (create j x),
    completedCreate_algebraicToCompleted i x,
    completedCreate_algebraicToCompleted j (create i x), ← map_add]
  have hcar : create i (create j x) + create j (create i x) = 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_create_create i j)
    simpa [ScalarExchange.zetaCommutator_apply] using h
  rw [hcar, map_zero]
  rfl

/-- Completed annihilation operators anticommute. -/
theorem completedAnticomm_annihilate_annihilate (i j : Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (completedAnnihilate i) (completedAnnihilate j) = 0 := by
  apply Common.continuousLinearMap_ext_algebraicCore
  intro x
  simp only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add, add_apply,
    mul_apply_eq_comp]
  rw [completedAnnihilate_algebraicToCompleted j x,
    completedAnnihilate_algebraicToCompleted i (annihilate j x),
    completedAnnihilate_algebraicToCompleted i x,
    completedAnnihilate_algebraicToCompleted j (annihilate i x), ← map_add]
  have hcar : annihilate i (annihilate j x) + annihilate j (annihilate i x) = 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_annihilate_annihilate i j)
    simpa [ScalarExchange.zetaCommutator_apply] using h
  rw [hcar, map_zero]
  rfl

/-- The mixed completed CAR: `{aᵢ, aⱼ†} = δᵢⱼ I`. -/
theorem completedAnticomm_annihilate_create (i j : Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (completedAnnihilate i) (completedCreate j) =
      if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0 := by
  apply Common.continuousLinearMap_ext_algebraicCore
  intro x
  simp only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add, add_apply,
    mul_apply_eq_comp]
  rw [completedCreate_algebraicToCompleted j x,
    completedAnnihilate_algebraicToCompleted i (create j x),
    completedAnnihilate_algebraicToCompleted i x,
    completedCreate_algebraicToCompleted j (annihilate i x), ← map_add]
  have hcar :
      annihilate i (create j x) + create j (annihilate i x) = if i = j then x else 0 := by
    have h := congrArg (fun f : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode => f x)
      (anticomm_annihilate_create i j)
    by_cases hij : i = j
    · simpa [ScalarExchange.zetaCommutator_apply, hij] using h
    · simpa [ScalarExchange.zetaCommutator_apply, hij] using h
  rw [hcar]
  by_cases hij : i = j <;> simp [hij]

/-- Creation-first form of the mixed completed CAR. -/
theorem completedAnticomm_create_annihilate (i j : Mode) :
    ScalarExchange.zetaCommutator (-1 : ℂ) (completedCreate i) (completedAnnihilate j) =
      if i = j then ContinuousLinearMap.id ℂ (CompletedFockSpace Mode) else 0 := by
  rw [ScalarExchange.zetaCommutator_swap_of_sq_eq_one
      (-1 : ℂ) (by norm_num) (completedAnnihilate j) (completedCreate i),
    completedAnticomm_annihilate_create]
  simp only [neg_neg, one_smul, eq_comm]


/-- The bounded one-mode occupation projection is exactly the completed
creation operator composed with annihilation. This identity is valid for
an arbitrary ordered mode type and does not require a finite Fock space. -/
theorem completedCreate_comp_completedAnnihilate_eq_numberOperator (i : Mode) :
    (completedCreate i).comp (completedAnnihilate i) = completedNumberOperator i := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  by_cases hi : i ∈ n
  · have hnot : i ∉ removeOccupation i n := by
      simp [removeOccupation]
    rw [ContinuousLinearMap.comp_apply, completedAnnihilate_basisState_of_mem hi,
      map_smul, completedCreate_basisState_of_not_mem hnot,
      completedNumberOperator_basisState, if_pos hi]
    have hphase : fermionPhase i (removeOccupation i n) = fermionPhase i n := by
      change (fermionSign i (removeOccupation i n) : ℂ) = (fermionSign i n : ℂ)
      rw [fermionSign_removeOccupation_of_not_lt (i := i) (k := i)
        (n := n) (lt_irrefl i)]
    rw [hphase]
    simp only [smul_smul, insertOccupation, removeOccupation, Finset.insert_erase hi]
    simp [fermionPhase, fermionSign_sq_complex]
  · simp [ContinuousLinearMap.comp_apply,
      completedAnnihilate_basisState_of_not_mem hi,
      completedNumberOperator_basisState, hi]

end
end Fermionic
end SecondQuantization
