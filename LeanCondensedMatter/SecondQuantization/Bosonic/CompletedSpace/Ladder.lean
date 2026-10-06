import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateIsometry

set_option linter.style.header false

/-!
# Bosonic ladder operators on completed Fock space

Bosonic creation and annihilation are unbounded on the completed occupation representation.  Their
natural domains are weighted `ℓ²` spaces:

- `aᵢ†`: `√(nᵢ + 1) ψₙ ∈ ℓ²`;
- `aᵢ`: `√nᵢ ψₙ ∈ ℓ²`.

The completed operators are therefore represented as `LinearPMap`s.  Creation first multiplies by
its square-root occupation weight and then extends the resulting coefficient sequence along the
injective occupation shift `n ↦ n + eᵢ`.  Annihilation multiplies by `√nᵢ` and then pulls the
sequence back along the same injection.

Both operators agree with the algebraic bosonic ladder operators on the finite-support core.
-/

namespace SecondQuantization
namespace Bosonic

open scoped ENNReal

noncomputable section

variable {Mode : Type*}

/-- Natural maximal weighted `ℓ²` domain of completed bosonic creation at mode `i`. -/
noncomputable abbrev completedCreateDomain (i : Mode) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain
    (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))

/-- Natural maximal weighted `ℓ²` domain of completed bosonic annihilation at mode `i`. -/
noncomputable abbrev completedAnnihilateDomain (i : Mode) :
    Submodule ℂ (CompletedFockSpace Mode) :=
  Common.completedDiagonalDomain
    (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))

/-- Completed bosonic creation on its maximal weighted `ℓ²` domain. -/
noncomputable def completedCreate (i : Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode where
  domain := completedCreateDomain i
  toFun :=
    (Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)).toLinearMap.comp
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))).toFun

/-- Completed bosonic annihilation on its maximal weighted `ℓ²` domain. -/
noncomputable def completedAnnihilate (i : Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode where
  domain := completedAnnihilateDomain i
  toFun :=
    (Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)).toLinearMap.comp
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))).toFun

/-- Coordinate action of completed bosonic creation.  A configuration with no particle in
mode `i` has no predecessor; otherwise the coefficient is shifted down by one occupation and
multiplied by the usual square-root factor. -/
@[simp]
theorem completedCreate_apply (i : Mode) (ψ : (completedCreate i).domain)
    (n : Occupation Mode) :
    completedCreate i ψ n =
      if n i = 0 then 0
      else (Real.sqrt (n i : ℝ) : ℂ) *
        (ψ : CompletedFockSpace Mode) (removeOccupation i n) := by
  classical
  change
    Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ)) ψ) n =
      _
  rw [Common.completedCoordinateEmbedding_apply]
  by_cases hni : n i = 0
  · rw [ite_eq_left hni, Function.extend_apply']
    · rfl
    · intro h
      rcases h with ⟨m, hm⟩
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hni] at hcoord
      omega
  · rw [ite_eq_right hni]
    have hrepr : createOccupation i (removeOccupation i n) = n :=
      createOccupation_removeOccupation_of_pos hni
    have hcoord : (removeOccupation i n) i + 1 = n i := by
      have h := congrArg (fun q : Occupation Mode => q i) hrepr
      simpa only [createOccupation_apply_same] using h
    have hcoord_real : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
      exact_mod_cast hcoord
    conv_lhs => rw [← hrepr]
    rw [(createOccupation_injective i).extend_apply,
      Common.completedDiagonalOperator_apply, hcoord_real]

/-- Coordinate action of completed bosonic annihilation. -/
@[simp]
theorem completedAnnihilate_apply (i : Mode) (ψ : (completedAnnihilate i).domain)
    (n : Occupation Mode) :
    completedAnnihilate i ψ n =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        (ψ : CompletedFockSpace Mode) (createOccupation i n) := by
  change
    Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ)) ψ) n =
      _
  rw [Common.completedCoordinatePullback_apply,
    Common.completedDiagonalOperator_apply,
    createOccupation_apply_same, Nat.cast_add, Nat.cast_one]

/-- Every occupation-basis vector belongs to the completed creation domain. -/
theorem completedBasisState_mem_completedCreateDomain (i : Mode) (n : Occupation Mode) :
    completedBasisState n ∈ completedCreateDomain i := by
  exact Common.completedBasisState_mem_completedDiagonalDomain
    (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ)) n

/-- Every occupation-basis vector belongs to the completed annihilation domain. -/
theorem completedBasisState_mem_completedAnnihilateDomain (i : Mode) (n : Occupation Mode) :
    completedBasisState n ∈ completedAnnihilateDomain i := by
  exact Common.completedBasisState_mem_completedDiagonalDomain
    (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ)) n

private theorem completedAnnihilatePullback_basisState_of_pos
    (i : Mode) {n : Occupation Mode} (hni : n i ≠ 0) :
    Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (completedBasisState n) =
      completedBasisState (removeOccupation i n) := by
  classical
  ext m
  rw [Common.completedCoordinatePullback_apply]
  by_cases hm : m = removeOccupation i n
  · subst m
    rw [createOccupation_removeOccupation_of_pos hni]
    simp [completedBasisState]
  · have hcreate : createOccupation i m ≠ n := by
      intro h
      apply hm
      have h' := congrArg (removeOccupation i) h
      simpa only [removeOccupation_createOccupation] using h'
    simp [completedBasisState, hcreate, hm]

private theorem completedCreateDiagonal_basisState (i : Mode) (n : Occupation Mode) :
    Common.completedDiagonalOperator
        (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ))
        ⟨completedBasisState n, completedBasisState_mem_completedCreateDomain i n⟩ =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) • completedBasisState n := by
  simpa [completedBasisState] using
    (Common.completedDiagonalOperator_basisState
      (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ)) n)

private theorem completedAnnihilateDiagonal_basisState (i : Mode) (n : Occupation Mode) :
    Common.completedDiagonalOperator
        (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ))
        ⟨completedBasisState n, completedBasisState_mem_completedAnnihilateDomain i n⟩ =
      (Real.sqrt (n i : ℝ) : ℂ) • completedBasisState n := by
  simpa [completedBasisState] using
    (Common.completedDiagonalOperator_basisState
      (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ)) n)

/-- Occupation-basis action of completed bosonic creation. -/
@[simp]
theorem completedCreate_basisState (i : Mode) (n : Occupation Mode)
    (h : completedBasisState n ∈ (completedCreate i).domain) :
    completedCreate i ⟨completedBasisState n, h⟩ =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) •
        completedBasisState (createOccupation i n) := by
  change
    Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ))
          ⟨completedBasisState n, h⟩) =
      _
  rw [completedCreateDiagonal_basisState, map_smul,
    Common.completedCoordinateEmbedding_basisState]

/-- Occupation-basis action of completed bosonic annihilation. -/
@[simp]
theorem completedAnnihilate_basisState (i : Mode) (n : Occupation Mode)
    (h : completedBasisState n ∈ (completedAnnihilate i).domain) :
    completedAnnihilate i ⟨completedBasisState n, h⟩ =
      (Real.sqrt (n i : ℝ) : ℂ) •
        completedBasisState (removeOccupation i n) := by
  change
    Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ))
          ⟨completedBasisState n, h⟩) =
      _
  rw [completedAnnihilateDiagonal_basisState, map_smul]
  by_cases hni : n i = 0
  · simp [hni]
  · rw [completedAnnihilatePullback_basisState_of_pos i hni]

private noncomputable def algebraicToCompletedCreateDomain (i : Mode) :
    FockSpace Mode →ₗ[ℂ] (completedCreate i).domain := by
  change FockSpace Mode →ₗ[ℂ] completedCreateDomain i
  exact Common.algebraicToCompletedDiagonalDomain
    (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))

private noncomputable def algebraicToCompletedAnnihilateDomain (i : Mode) :
    FockSpace Mode →ₗ[ℂ] (completedAnnihilate i).domain := by
  change FockSpace Mode →ₗ[ℂ] completedAnnihilateDomain i
  exact Common.algebraicToCompletedDiagonalDomain
    (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))

private theorem algebraicToCompleted_basisState' (n : Occupation Mode) :
    algebraicToCompleted (basisState n) = completedBasisState n := by
  simpa [algebraicToCompleted, basisState, completedBasisState] using
    (Common.algebraicToCompleted_basisState (Config := Occupation Mode) n)

/-- On the finite-support core, completed bosonic creation agrees with the algebraic creation
operator. -/
theorem completedCreate_comp_algebraicCore (i : Mode) :
    (completedCreate i).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))) =
      algebraicToCompleted.comp (create i) := by
  change
    (completedCreate i).toFun.comp (algebraicToCompletedCreateDomain i) =
      algebraicToCompleted.comp (create i)
  apply Common.linearMap_ext_basisState
  intro n
  simp only [LinearMap.comp_apply]
  change
    (completedCreate i).toFun (algebraicToCompletedCreateDomain i (basisState n)) =
      algebraicToCompleted (create i (basisState n))
  have hmem : completedBasisState n ∈ (completedCreate i).domain := by
    change completedBasisState n ∈ completedCreateDomain i
    exact completedBasisState_mem_completedCreateDomain i n
  have hdomain :
      algebraicToCompletedCreateDomain i (basisState n) =
        ⟨completedBasisState n, hmem⟩ := by
    apply Subtype.ext
    exact algebraicToCompleted_basisState' n
  rw [hdomain, LinearPMap.toFun_eq_coe, completedCreate_basisState,
    create_basisState_eq, map_smul, algebraicToCompleted_basisState']

/-- On the finite-support core, completed bosonic annihilation agrees with the algebraic
annihilation operator. -/
theorem completedAnnihilate_comp_algebraicCore (i : Mode) :
    (completedAnnihilate i).toFun.comp
        (Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))) =
      algebraicToCompleted.comp (annihilate i) := by
  change
    (completedAnnihilate i).toFun.comp (algebraicToCompletedAnnihilateDomain i) =
      algebraicToCompleted.comp (annihilate i)
  apply Common.linearMap_ext_basisState
  intro n
  simp only [LinearMap.comp_apply]
  change
    (completedAnnihilate i).toFun (algebraicToCompletedAnnihilateDomain i (basisState n)) =
      algebraicToCompleted (annihilate i (basisState n))
  have hmem : completedBasisState n ∈ (completedAnnihilate i).domain := by
    change completedBasisState n ∈ completedAnnihilateDomain i
    exact completedBasisState_mem_completedAnnihilateDomain i n
  have hdomain :
      algebraicToCompletedAnnihilateDomain i (basisState n) =
        ⟨completedBasisState n, hmem⟩ := by
    apply Subtype.ext
    exact algebraicToCompleted_basisState' n
  rw [hdomain, LinearPMap.toFun_eq_coe, completedAnnihilate_basisState,
    annihilate_basisState_eq, map_smul, algebraicToCompleted_basisState']

end
end Bosonic
end SecondQuantization
