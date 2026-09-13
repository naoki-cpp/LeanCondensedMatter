import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Coordinate isometries on completed Fock space

Configuration equivalences act on the generic completed Fock space by reindexing coordinates, and
unit-modulus scalar functions act through bounded diagonal multiplication. Both constructions
preserve the `ℓ²` norm and are bundled as linear isometries.

Statistics-specific completed-space operators should specialize these constructions and keep only
their occupation, sign, or other model-specific semantics locally.
-/

namespace SecondQuantization
namespace Common

open scoped ENNReal

noncomputable section

variable {Config : Type*}

private noncomputable def completedReindexLinear (e : Config ≃ Config) :
    CompletedFock Config →ₗ[ℂ] CompletedFock Config where
  toFun ψ := by
    refine ⟨fun c => ψ (e c), ?_⟩
    apply memℓp_gen
    have hψ := (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa [Function.comp_def] using hψ.comp_injective e.injective
  map_add' ψ φ := by
    ext c
    rfl
  map_smul' a ψ := by
    ext c
    rfl

@[simp]
private theorem completedReindexLinear_apply (e : Config ≃ Config)
    (ψ : CompletedFock Config) (c : Config) :
    completedReindexLinear e ψ c = ψ (e c) :=
  rfl

private theorem norm_completedReindexLinear_le (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    ‖completedReindexLinear e ψ‖ ≤ ‖ψ‖ := by
  apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg ψ)
  rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ]
  exact le_of_eq <| by
    simpa [completedReindexLinear_apply] using
      (Equiv.tsum_eq e (fun c : Config => ‖ψ c‖ ^ (2 : ℝ≥0∞).toReal))

@[simp]
private theorem completedReindexLinear_symm_apply (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    completedReindexLinear e.symm (completedReindexLinear e ψ) = ψ := by
  ext c
  simp

private theorem norm_completedReindexLinear (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    ‖completedReindexLinear e ψ‖ = ‖ψ‖ := by
  apply le_antisymm (norm_completedReindexLinear_le e ψ)
  simpa using norm_completedReindexLinear_le e.symm (completedReindexLinear e ψ)

/-- Reindex completed Fock amplitudes along a configuration equivalence. -/
noncomputable def completedReindex (e : Config ≃ Config) :
    CompletedFock Config →ₗᵢ[ℂ] CompletedFock Config :=
  { completedReindexLinear e with
    norm_map' := norm_completedReindexLinear e }

@[simp]
theorem completedReindex_apply (e : Config ≃ Config) (ψ : CompletedFock Config)
    (c : Config) :
    completedReindex e ψ c = ψ (e c) :=
  rfl

@[simp]
theorem completedReindex_basisState (e : Config ≃ Config) (c : Config) :
    completedReindex e (completedBasisState c) = completedBasisState (e.symm c) := by
  classical
  ext d
  rw [completedReindex_apply]
  by_cases h : d = e.symm c
  · subst d
    simp
  · have hed : e d ≠ c := by
      intro he
      apply h
      exact e.injective <| by simpa using he
    simp [completedBasisState_apply_of_ne h, completedBasisState_apply_of_ne hed]

private theorem completedPhaseMultiplier_bound
    (phase : Config → ℂ) (hphase : ∀ c, ‖phase c‖ = 1) (c : Config) :
    ‖phase c‖ ≤ 1 := by
  simp [hphase c]

private theorem norm_completedPhaseMultiplier
    (phase : Config → ℂ) (hphase : ∀ c, ‖phase c‖ = 1)
    (ψ : CompletedFock Config) :
    ‖completedBoundedDiagonalOperator phase zero_le_one
        (completedPhaseMultiplier_bound phase hphase) ψ‖ = ‖ψ‖ := by
  apply le_antisymm
  · simpa only [one_mul] using
      norm_completedBoundedDiagonalOperator_apply_le phase zero_le_one
        (completedPhaseMultiplier_bound phase hphase) ψ
  · exact lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      (x := ψ)
      (y := completedBoundedDiagonalOperator phase zero_le_one
        (completedPhaseMultiplier_bound phase hphase) ψ) fun c => by
        rw [completedBoundedDiagonalOperator_apply]
        simp [hphase c]

/-- Coordinatewise multiplication by a unit-modulus complex phase as a linear isometry. -/
noncomputable def completedPhaseMultiplier
    (phase : Config → ℂ) (hphase : ∀ c, ‖phase c‖ = 1) :
    CompletedFock Config →ₗᵢ[ℂ] CompletedFock Config :=
  { (completedBoundedDiagonalOperator phase zero_le_one
      (completedPhaseMultiplier_bound phase hphase)).toLinearMap with
    norm_map' := norm_completedPhaseMultiplier phase hphase }

@[simp]
theorem completedPhaseMultiplier_apply
    (phase : Config → ℂ) (hphase : ∀ c, ‖phase c‖ = 1)
    (ψ : CompletedFock Config) (c : Config) :
    completedPhaseMultiplier phase hphase ψ c = phase c * ψ c := by
  change completedBoundedDiagonalOperator phase zero_le_one
      (completedPhaseMultiplier_bound phase hphase) ψ c = _
  rw [completedBoundedDiagonalOperator_apply]

@[simp]
theorem completedPhaseMultiplier_basisState
    (phase : Config → ℂ) (hphase : ∀ c, ‖phase c‖ = 1) (c : Config) :
    completedPhaseMultiplier phase hphase (completedBasisState c) =
      phase c • completedBasisState c := by
  change completedBoundedDiagonalOperator phase zero_le_one
      (completedPhaseMultiplier_bound phase hphase) (completedBasisState c) = _
  exact completedBoundedDiagonalOperator_basisState phase zero_le_one
    (completedPhaseMultiplier_bound phase hphase) c

end
end Common
end SecondQuantization
