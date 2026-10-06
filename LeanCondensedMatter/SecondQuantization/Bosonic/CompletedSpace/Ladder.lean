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
  by_cases hni : n i = 0
  · rw [ite_eq_left hni]
    change
      Function.extend (createOccupation i)
          (fun m => (Real.sqrt (m i + 1 : ℝ) : ℂ) *
            (ψ : CompletedFockSpace Mode) m) 0 n = 0
    rw [Function.extend_apply']
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
    change
      Function.extend (createOccupation i)
          (fun m => (Real.sqrt (m i + 1 : ℝ) : ℂ) *
            (ψ : CompletedFockSpace Mode) m) 0 n =
        (Real.sqrt (n i : ℝ) : ℂ) *
          (ψ : CompletedFockSpace Mode) (removeOccupation i n)
    conv_lhs => rw [← hrepr]
    rw [(createOccupation_injective i).extend_apply, hcoord_real]

/-- Coordinate action of completed bosonic annihilation. -/
@[simp]
theorem completedAnnihilate_apply (i : Mode) (ψ : (completedAnnihilate i).domain)
    (n : Occupation Mode) :
    completedAnnihilate i ψ n =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        (ψ : CompletedFockSpace Mode) (createOccupation i n) := by
  change
    (Real.sqrt ((createOccupation i n) i : ℝ) : ℂ) *
        (ψ : CompletedFockSpace Mode) (createOccupation i n) =
      _
  rw [createOccupation_apply_same, Nat.cast_add, Nat.cast_one]

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

/-- Occupation-basis action of completed bosonic creation. -/
@[simp]
theorem completedCreate_basisState (i : Mode) (n : Occupation Mode)
    (h : completedBasisState n ∈ (completedCreate i).domain) :
    completedCreate i ⟨completedBasisState n, h⟩ =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) •
        completedBasisState (createOccupation i n) := by
  classical
  ext m
  rw [completedCreate_apply]
  by_cases hmi : m i = 0
  · rw [ite_eq_left hmi]
    have hne : m ≠ createOccupation i n := by
      intro hm
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hmi] at hcoord
      omega
    simpa [completedBasisState] using
      congrArg
        (fun z : ℂ => (Real.sqrt (n i + 1 : ℝ) : ℂ) * z)
        (Common.completedBasisState_apply_of_ne
          (Config := Occupation Mode) hne)
  · rw [ite_eq_right hmi]
    by_cases hm : m = createOccupation i n
    · subst m
      rw [removeOccupation_createOccupation]
      simp [completedBasisState, createOccupation_apply_same, Nat.cast_add, Nat.cast_one]
    · have hremove : removeOccupation i m ≠ n := by
        intro hr
        apply hm
        calc
          m = createOccupation i (removeOccupation i m) :=
            (createOccupation_removeOccupation_of_pos hmi).symm
          _ = createOccupation i n := congrArg (createOccupation i) hr
      have hleft :
          completedBasisState n (removeOccupation i m) = 0 := by
        simpa [completedBasisState] using
          (Common.completedBasisState_apply_of_ne
            (Config := Occupation Mode) hremove)
      have hright :
          completedBasisState (createOccupation i n) m = 0 := by
        simpa [completedBasisState] using
          (Common.completedBasisState_apply_of_ne
            (Config := Occupation Mode) hm)
      simp [hleft, hright]

/-- Occupation-basis action of completed bosonic annihilation. -/
@[simp]
theorem completedAnnihilate_basisState (i : Mode) (n : Occupation Mode)
    (h : completedBasisState n ∈ (completedAnnihilate i).domain) :
    completedAnnihilate i ⟨completedBasisState n, h⟩ =
      (Real.sqrt (n i : ℝ) : ℂ) •
        completedBasisState (removeOccupation i n) := by
  classical
  ext m
  rw [completedAnnihilate_apply]
  by_cases hni : n i = 0
  · have hne : createOccupation i m ≠ n := by
      intro hm
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hni] at hcoord
      omega
    have hleft :
        completedBasisState n (createOccupation i m) = 0 := by
      simpa [completedBasisState] using
        (Common.completedBasisState_apply_of_ne
          (Config := Occupation Mode) hne)
    simp [hni, hleft]
  · by_cases hm : m = removeOccupation i n
    · subst m
      rw [createOccupation_removeOccupation_of_pos hni]
      have hcoord : (removeOccupation i n) i + 1 = n i := by
        rw [removeOccupation_apply_same]
        omega
      have hcoord_real : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
        exact_mod_cast hcoord
      rw [hcoord_real]
      simp [completedBasisState]
    · have hcreate : createOccupation i m ≠ n := by
        intro hc
        apply hm
        have h' := congrArg (removeOccupation i) hc
        simpa only [removeOccupation_createOccupation] using h'
      have hleft :
          completedBasisState n (createOccupation i m) = 0 := by
        simpa [completedBasisState] using
          (Common.completedBasisState_apply_of_ne
            (Config := Occupation Mode) hcreate)
      have hright :
          completedBasisState (removeOccupation i n) m = 0 := by
        simpa [completedBasisState] using
          (Common.completedBasisState_apply_of_ne
            (Config := Occupation Mode) hm)
      simp [hleft, hright]

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
    exact algebraicToCompleted_basisState n
  rw [hdomain, LinearPMap.toFun_eq_coe, completedCreate_basisState,
    create_basisState_eq, map_smul, algebraicToCompleted_basisState]

/-- On the finite-support core, completed bosonic annihilation agrees with the algebraic
annihilation operator. -/
theorem completedAnnihilate_comp_algebraicCore (i : Mode) :
    (completedAnnihilate i).toFun.comp (algebraicToCompletedAnnihilateDomain i) =
      algebraicToCompleted.comp (annihilate i) := by
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
    exact algebraicToCompleted_basisState n
  rw [hdomain, LinearPMap.toFun_eq_coe, completedAnnihilate_basisState,
    annihilate_basisState_eq, map_smul, algebraicToCompleted_basisState]

end
end Bosonic
end SecondQuantization
