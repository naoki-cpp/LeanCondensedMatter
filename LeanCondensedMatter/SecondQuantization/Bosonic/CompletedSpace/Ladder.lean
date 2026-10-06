import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

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

/-- Zero-extension of a completed coefficient sequence along the injective creation occupation map. -/
private noncomputable def completedCreateExtension (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨Function.extend (createOccupation i) (fun n => ψ n) 0, ?_⟩
    apply memℓp_gen
    refine ((createOccupation_injective i).summable_iff ?_).mp ?_
    · intro m hm
      rw [Function.extend_apply']
      · simp
      · intro h
        exact hm h
    · have hsum :=
        (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      exact hsum.congr fun n => by
        simp only [Function.comp_apply]
        rw [(createOccupation_injective i).extend_apply]
  map_add' ψ φ := by
    apply Subtype.ext
    funext m
    change
      Function.extend (createOccupation i) (fun n => (ψ + φ) n) 0 m =
        Function.extend (createOccupation i) (fun n => ψ n) 0 m +
          Function.extend (createOccupation i) (fun n => φ n) 0 m
    by_cases hm : m ∈ Set.range (createOccupation i)
    · rcases hm with ⟨n, rfl⟩
      rw [(createOccupation_injective i).extend_apply,
        (createOccupation_injective i).extend_apply,
        (createOccupation_injective i).extend_apply]
      rfl
    · have hnot : ¬ ∃ n, createOccupation i n = m := hm
      rw [Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot]
      simp
  map_smul' a ψ := by
    apply Subtype.ext
    funext m
    change
      Function.extend (createOccupation i) (fun n => (a • ψ) n) 0 m =
        a • Function.extend (createOccupation i) (fun n => ψ n) 0 m
    by_cases hm : m ∈ Set.range (createOccupation i)
    · rcases hm with ⟨n, rfl⟩
      rw [(createOccupation_injective i).extend_apply,
        (createOccupation_injective i).extend_apply]
      rfl
    · have hnot : ¬ ∃ n, createOccupation i n = m := hm
      rw [Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot]
      simp

/-- Pullback of a completed coefficient sequence along the injective creation occupation map. -/
private noncomputable def completedAnnihilatePullback (i : Mode) :
    CompletedFockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode where
  toFun ψ := by
    refine ⟨fun n => ψ (createOccupation i n), ?_⟩
    apply memℓp_gen
    have hsum :=
      (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa [Function.comp_def] using
      hsum.comp_injective (createOccupation_injective i)
  map_add' ψ φ := by
    ext n
    rfl
  map_smul' a ψ := by
    ext n
    rfl

/-- Completed bosonic creation on its maximal weighted `ℓ²` domain. -/
noncomputable def completedCreate (i : Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode where
  domain := completedCreateDomain i
  toFun :=
    (completedCreateExtension i).comp
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))).toFun

/-- Completed bosonic annihilation on its maximal weighted `ℓ²` domain. -/
noncomputable def completedAnnihilate (i : Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode where
  domain := completedAnnihilateDomain i
  toFun :=
    (completedAnnihilatePullback i).comp
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))).toFun

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

private theorem completedCreateExtension_basisState (i : Mode) (n : Occupation Mode) :
    completedCreateExtension i (completedBasisState n) =
      completedBasisState (createOccupation i n) := by
  classical
  ext m
  by_cases hm : m ∈ Set.range (createOccupation i)
  · rcases hm with ⟨k, rfl⟩
    change
      Function.extend (createOccupation i)
          (fun q => completedBasisState n q) 0 (createOccupation i k) =
        completedBasisState (createOccupation i n) (createOccupation i k)
    rw [(createOccupation_injective i).extend_apply]
    by_cases hkn : k = n
    · subst k
      rw [completedBasisState_apply_self, completedBasisState_apply_self]
    · have hshift :
          createOccupation i k ≠ createOccupation i n :=
        (createOccupation_injective i).ne hkn
      rw [completedBasisState_apply_of_ne hkn,
        completedBasisState_apply_of_ne hshift]
  · change
      Function.extend (createOccupation i)
          (fun q => completedBasisState n q) 0 m =
        completedBasisState (createOccupation i n) m
    have hne : m ≠ createOccupation i n := by
      intro h
      apply hm
      exact ⟨n, h.symm⟩
    rw [Function.extend_apply']
    · simp [completedBasisState_apply_of_ne hne]
    · intro h
      exact hm h

private theorem completedAnnihilatePullback_basisState_of_pos
    (i : Mode) {n : Occupation Mode} (hni : n i ≠ 0) :
    completedAnnihilatePullback i (completedBasisState n) =
      completedBasisState (removeOccupation i n) := by
  classical
  ext m
  change
    completedBasisState n (createOccupation i m) =
      completedBasisState (removeOccupation i n) m
  by_cases hm : m = removeOccupation i n
  · subst m
    rw [createOccupation_removeOccupation_of_pos hni,
      completedBasisState_apply_self, completedBasisState_apply_self]
  · have hcreate : createOccupation i m ≠ n := by
      intro h
      apply hm
      have h' := congrArg (removeOccupation i) h
      simpa only [removeOccupation_createOccupation] using h'
    rw [completedBasisState_apply_of_ne hcreate,
      completedBasisState_apply_of_ne hm]

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
theorem completedCreate_basisState (i : Mode) (n : Occupation Mode) :
    completedCreate i
        ⟨completedBasisState n, completedBasisState_mem_completedCreateDomain i n⟩ =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) •
        completedBasisState (createOccupation i n) := by
  change
    completedCreateExtension i
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i + 1 : ℝ) : ℂ))
          ⟨completedBasisState n, completedBasisState_mem_completedCreateDomain i n⟩) =
      _
  rw [completedCreateDiagonal_basisState, map_smul,
    completedCreateExtension_basisState]

/-- Occupation-basis action of completed bosonic annihilation. -/
@[simp]
theorem completedAnnihilate_basisState (i : Mode) (n : Occupation Mode) :
    completedAnnihilate i
        ⟨completedBasisState n, completedBasisState_mem_completedAnnihilateDomain i n⟩ =
      (Real.sqrt (n i : ℝ) : ℂ) •
        completedBasisState (removeOccupation i n) := by
  change
    completedAnnihilatePullback i
        (Common.completedDiagonalOperator
          (fun m : Occupation Mode => (Real.sqrt (m i : ℝ) : ℂ))
          ⟨completedBasisState n, completedBasisState_mem_completedAnnihilateDomain i n⟩) =
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

/-- On the finite-support core, completed bosonic creation agrees with the algebraic creation
operator. -/
theorem completedCreate_comp_algebraicCore (i : Mode) :
    (completedCreate i).toFun.comp (algebraicToCompletedCreateDomain i) =
      algebraicToCompleted.comp (create i) := by
  apply Common.linearMap_ext_basisState
  intro n
  simp only [LinearMap.comp_apply]
  have hdomain :
      algebraicToCompletedCreateDomain i (basisState n) =
        ⟨completedBasisState n, completedBasisState_mem_completedCreateDomain i n⟩ := by
    apply Subtype.ext
    exact algebraicToCompleted_basisState n
  rw [hdomain, completedCreate_basisState, create_basisState_eq,
    map_smul, algebraicToCompleted_basisState]

/-- On the finite-support core, completed bosonic annihilation agrees with the algebraic
annihilation operator. -/
theorem completedAnnihilate_comp_algebraicCore (i : Mode) :
    (completedAnnihilate i).toFun.comp (algebraicToCompletedAnnihilateDomain i) =
      algebraicToCompleted.comp (annihilate i) := by
  apply Common.linearMap_ext_basisState
  intro n
  simp only [LinearMap.comp_apply]
  have hdomain :
      algebraicToCompletedAnnihilateDomain i (basisState n) =
        ⟨completedBasisState n, completedBasisState_mem_completedAnnihilateDomain i n⟩ := by
    apply Subtype.ext
    exact algebraicToCompleted_basisState n
  rw [hdomain, completedAnnihilate_basisState, annihilate_basisState_eq,
    map_smul, algebraicToCompleted_basisState]

end
end Bosonic
end SecondQuantization
