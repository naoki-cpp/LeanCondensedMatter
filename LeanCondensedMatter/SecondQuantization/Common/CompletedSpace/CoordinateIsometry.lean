import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Coordinate isometries on completed Fock space

Configuration equivalences act on the generic completed Fock space by reindexing coordinates.
Injective configuration maps give isometric zero-extension embeddings, whose bounded adjoints are
the corresponding coordinate pullbacks. Unit-modulus scalar functions act through bounded diagonal
multiplication. The norm-preserving constructions are bundled as linear isometries.

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

private theorem norm_completedReindexLinear_le (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    ‖completedReindexLinear e ψ‖ ≤ ‖ψ‖ := by
  apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg ψ)
  rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ]
  exact le_of_eq <| by
    simpa [completedReindexLinear] using
      (Equiv.tsum_eq e (fun c : Config => ‖ψ c‖ ^ (2 : ℝ≥0∞).toReal))

private theorem completedReindexLinear_symm_apply (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    completedReindexLinear e.symm (completedReindexLinear e ψ) = ψ := by
  ext c
  simp [completedReindexLinear]

private theorem norm_completedReindexLinear (e : Config ≃ Config)
    (ψ : CompletedFock Config) :
    ‖completedReindexLinear e ψ‖ = ‖ψ‖ := by
  apply le_antisymm (norm_completedReindexLinear_le e ψ)
  simpa [completedReindexLinear_symm_apply] using
    norm_completedReindexLinear_le e.symm (completedReindexLinear e ψ)

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

variable {Config' : Type*}

/-- Zero-extension of completed amplitudes along an injective configuration map. -/
private noncomputable def completedCoordinateEmbeddingLinear
    (f : Config → Config') (hf : Function.Injective f) :
    CompletedFock Config →ₗ[ℂ] CompletedFock Config' where
  toFun ψ := by
    refine ⟨Function.extend f (fun c => ψ c) 0, ?_⟩
    apply memℓp_gen
    refine (hf.summable_iff ?_).mp ?_
    · intro c hc
      rw [Function.extend_apply']
      · simp
      · exact hc
    · have hsum :=
        (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      exact hsum.congr fun c => by
        simp only [Function.comp_apply]
        rw [hf.extend_apply]
  map_add' ψ φ := by
    apply Subtype.ext
    funext c
    change
      Function.extend f (fun d => (ψ + φ) d) 0 c =
        Function.extend f (fun d => ψ d) 0 c +
          Function.extend f (fun d => φ d) 0 c
    by_cases hc : c ∈ Set.range f
    · rcases hc with ⟨d, rfl⟩
      simp only [hf.extend_apply]
      rfl
    · have hnot : ¬ ∃ d, f d = c := hc
      rw [Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot]
      simp
  map_smul' a ψ := by
    apply Subtype.ext
    funext c
    change
      Function.extend f (fun d => (a • ψ) d) 0 c =
        a • Function.extend f (fun d => ψ d) 0 c
    by_cases hc : c ∈ Set.range f
    · rcases hc with ⟨d, rfl⟩
      simp only [hf.extend_apply]
      rfl
    · have hnot : ¬ ∃ d, f d = c := hc
      rw [Function.extend_apply' _ _ _ hnot,
        Function.extend_apply' _ _ _ hnot]
      simp

private theorem completedCoordinateEmbedding_tsum_norm_rpow
    (f : Config → Config') (hf : Function.Injective f)
    (ψ : CompletedFock Config) :
    (∑' c : Config',
        ‖completedCoordinateEmbeddingLinear f hf ψ c‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' c : Config, ‖ψ c‖ ^ (2 : ℝ≥0∞).toReal := by
  have hsum :=
    (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hext :
      HasSum
        (Function.extend f
          (fun c : Config => ‖ψ c‖ ^ (2 : ℝ≥0∞).toReal) 0)
        (∑' c : Config, ‖ψ c‖ ^ (2 : ℝ≥0∞).toReal) :=
    (hasSum_extend_zero hf).2 hsum.hasSum
  rw [← hext.tsum_eq]
  apply tsum_congr
  intro c
  by_cases hc : c ∈ Set.range f
  · rcases hc with ⟨d, rfl⟩
    change
      ‖Function.extend f (fun q => ψ q) 0 (f d)‖ ^ (2 : ℝ≥0∞).toReal =
        Function.extend f
          (fun q : Config => ‖ψ q‖ ^ (2 : ℝ≥0∞).toReal) 0 (f d)
    rw [hf.extend_apply, hf.extend_apply]
  · have hnot : ¬ ∃ d, f d = c := hc
    change
      ‖Function.extend f (fun q => ψ q) 0 c‖ ^ (2 : ℝ≥0∞).toReal =
        Function.extend f
          (fun q : Config => ‖ψ q‖ ^ (2 : ℝ≥0∞).toReal) 0 c
    rw [Function.extend_apply' _ _ _ hnot,
      Function.extend_apply' _ _ _ hnot]
    simp

private theorem norm_completedCoordinateEmbeddingLinear
    (f : Config → Config') (hf : Function.Injective f)
    (ψ : CompletedFock Config) :
    ‖completedCoordinateEmbeddingLinear f hf ψ‖ = ‖ψ‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg ψ)
    rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ]
    exact le_of_eq (completedCoordinateEmbedding_tsum_norm_rpow f hf ψ)
  · apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by norm_num)
      (norm_nonneg (completedCoordinateEmbeddingLinear f hf ψ))
    rw [lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (completedCoordinateEmbeddingLinear f hf ψ)]
    exact le_of_eq (completedCoordinateEmbedding_tsum_norm_rpow f hf ψ).symm

/-- Embed completed amplitudes isometrically by zero-extension along an injective configuration map. -/
noncomputable def completedCoordinateEmbedding
    (f : Config → Config') (hf : Function.Injective f) :
    CompletedFock Config →ₗᵢ[ℂ] CompletedFock Config' :=
  { completedCoordinateEmbeddingLinear f hf with
    norm_map' := norm_completedCoordinateEmbeddingLinear f hf }

@[simp]
theorem completedCoordinateEmbedding_apply
    (f : Config → Config') (hf : Function.Injective f)
    (ψ : CompletedFock Config) (c : Config') :
    completedCoordinateEmbedding f hf ψ c =
      Function.extend f (fun d => ψ d) 0 c :=
  rfl

@[simp]
theorem completedCoordinateEmbedding_basisState
    (f : Config → Config') (hf : Function.Injective f) (c : Config) :
    completedCoordinateEmbedding f hf (completedBasisState c) =
      completedBasisState (f c) := by
  classical
  ext d
  rw [completedCoordinateEmbedding_apply]
  by_cases hd : d ∈ Set.range f
  · rcases hd with ⟨q, rfl⟩
    rw [hf.extend_apply]
    by_cases hqc : q = c
    · subst q
      simp
    · have hfc : f q ≠ f c := hf.ne hqc
      simp [completedBasisState_apply_of_ne hqc,
        completedBasisState_apply_of_ne hfc]
  · have hnot : ¬ ∃ q, f q = d := hd
    have hne : d ≠ f c := by
      intro h
      apply hd
      exact ⟨c, h.symm⟩
    rw [Function.extend_apply' _ _ _ hnot]
    simp [completedBasisState_apply_of_ne hne]

/-- Pull completed amplitudes back along an injective configuration map.

This is the Hilbert-space adjoint of zero-extension along that map. -/
noncomputable def completedCoordinatePullback
    (f : Config → Config') (hf : Function.Injective f) :
    CompletedFock Config' →L[ℂ] CompletedFock Config :=
  ContinuousLinearMap.adjoint (completedCoordinateEmbedding f hf).toContinuousLinearMap

@[simp]
theorem completedCoordinatePullback_apply
    (f : Config → Config') (hf : Function.Injective f)
    (ψ : CompletedFock Config') (c : Config) :
    completedCoordinatePullback f hf ψ c = ψ (f c) := by
  rw [← inner_completedBasisState_left c]
  change
    inner ℂ (completedBasisState c)
        (ContinuousLinearMap.adjoint
          (completedCoordinateEmbedding f hf).toContinuousLinearMap ψ) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    inner ℂ
        (completedCoordinateEmbedding f hf (completedBasisState c)) ψ =
      ψ (f c)
  rw [completedCoordinateEmbedding_basisState,
    inner_completedBasisState_left]

@[simp]
theorem completedCoordinateEmbedding_adjoint
    (f : Config → Config') (hf : Function.Injective f) :
    ContinuousLinearMap.adjoint
        (completedCoordinateEmbedding f hf).toContinuousLinearMap =
      completedCoordinatePullback f hf :=
  rfl

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
