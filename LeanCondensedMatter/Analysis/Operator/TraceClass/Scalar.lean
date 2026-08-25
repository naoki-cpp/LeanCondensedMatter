import LeanCondensedMatter.Analysis.Operator.TraceClass.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv

set_option linter.style.header false

/-!
# Spectral trace under scalar multiplication

Proves that spectral summability is preserved under nonzero real scalar multiplication and that
`spectralTrace` is homogeneous. See `notes/roadmaps/operator-algebra.md`.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- Scaling `T` by a nonzero real `c` scales each eigenvalue by `c` and leaves the
eigenspaces unchanged. -/
theorem eigenspace_smul {c : ℝ} (hc : c ≠ 0) (μ : ℂ) :
    Module.End.eigenspace (((c • T : H →L[ℂ] H)) : H →ₗ[ℂ] H) ((c : ℂ) * μ) =
      Module.End.eigenspace (T : H →ₗ[ℂ] H) μ := by
  let f : Module.End ℂ H := (T : H →ₗ[ℂ] H)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  change Module.End.eigenspace ((c : ℂ) • f) ((c : ℂ) * μ) =
    Module.End.eigenspace f μ
  have hdiv := Module.End.eigenspace_div f ((c : ℂ) * μ) (c : ℂ) hc'
  simp only [Algebra.algebraMap_eq_smul_one] at hdiv
  rw [Module.End.eigenspace_def, ← hdiv]
  simp [hc']

private noncomputable def eigenvalueScaleEquiv {c : ℝ} (hc : c ≠ 0) :
    { μ : ℝ // μ ≠ 0 } ≃ { μ : ℝ // μ ≠ 0 } :=
  (Equiv.mulLeft₀ c hc).subtypeEquiv fun μ => by
    constructor
    · exact mul_ne_zero hc
    · intro h hμ
      apply h
      simp [hμ]

@[simp] private theorem eigenvalueScaleEquiv_apply {c : ℝ} (hc : c ≠ 0)
    (a : { μ : ℝ // μ ≠ 0 }) :
    ((eigenvalueScaleEquiv hc a : { μ : ℝ // μ ≠ 0 }) : ℝ) = c * a.1 := rfl

omit [CompleteSpace H] in
/-- Spectral summability is preserved under multiplication by a nonzero real scalar. -/
theorem hasSummableRealEigenvalues_smul {c : ℝ} (hc : c ≠ 0)
    (h : HasSummableRealEigenvalues T) : HasSummableRealEigenvalues (c • T) := by
  set e := eigenvalueScaleEquiv hc with he_def
  have hfin : ∀ μ : { γ : ℝ // γ ≠ 0 },
      Module.finrank ℂ (Module.End.eigenspace ((c • T : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ.1 : ℂ)) =
      Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) ((e.symm μ).1 : ℂ)) := by
    intro μ
    have h2 := congrArg Subtype.val (e.apply_symm_apply μ)
    rw [he_def, eigenvalueScaleEquiv_apply] at h2
    have heq : (μ.1 : ℂ) = (c : ℂ) * ((e.symm μ).1 : ℂ) := by exact_mod_cast h2.symm
    rw [heq, eigenspace_smul hc]
  have hval : ∀ μ : { γ : ℝ // γ ≠ 0 }, μ.1 = c * (e.symm μ).1 := by
    intro μ
    have h2 := congrArg Subtype.val (e.apply_symm_apply μ)
    rw [he_def, eigenvalueScaleEquiv_apply] at h2
    linarith
  have hT' : Summable (fun ν : { γ : ℝ // γ ≠ 0 } =>
      (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (ν.1 : ℂ)) : ℝ) * |ν.1|) := by
    have hsig := (summable_sigma_of_nonneg (f := fun a : EigenvectorIndex T => |a.1.1|)
      (fun a => abs_nonneg _)).mp h
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hsig.2
  change Summable (fun a : EigenvectorIndex (c • T) => |a.1.1|)
  apply (summable_sigma_of_nonneg (f := fun a : EigenvectorIndex (c • T) => |a.1.1|)
    (fun a => abs_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  have heq2 : (fun μ : { γ : ℝ // γ ≠ 0 } =>
      ∑' _i : Fin (Module.finrank ℂ (Module.End.eigenspace ((c • T : H →L[ℂ] H) : H →ₗ[ℂ] H)
        (μ.1 : ℂ))), |μ.1|) =
      (fun μ => |c| * ((Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H)
        ((e.symm μ).1 : ℂ)) : ℝ) * |(e.symm μ).1|)) := by
    funext μ
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hfin μ, hval μ,
      abs_mul]
    ring
  rw [heq2]
  refine (summable_mul_left_iff (abs_ne_zero.mpr hc)).mpr ?_
  rw [show (fun μ : { γ : ℝ // γ ≠ 0 } => (Module.finrank ℂ (Module.End.eigenspace
      (T : H →ₗ[ℂ] H) ((e.symm μ).1 : ℂ)) : ℝ) * |(e.symm μ).1|) =
      (fun ν : { γ : ℝ // γ ≠ 0 } =>
        (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (ν.1 : ℂ)) : ℝ) * |ν.1|) ∘
        ⇑e.symm from rfl]
  exact (Equiv.summable_iff e.symm).mpr hT'

omit [CompleteSpace H] in
/-- `spectralTrace` is homogeneous under multiplication by a nonzero real scalar. -/
theorem spectralTrace_smul {c : ℝ} (hc : c ≠ 0) (h : HasSummableRealEigenvalues T)
    (hcT : HasSummableRealEigenvalues (c • T)) :
    spectralTrace (c • T) = c * spectralTrace T := by
  change (∑' b : EigenvectorIndex (c • T), b.1.1) = c * ∑' a : EigenvectorIndex T, a.1.1
  rw [tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex hcT),
    tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex h),
    ← (eigenvalueScaleEquiv hc).tsum_eq (fun ν : { γ : ℝ // γ ≠ 0 } =>
      (Module.finrank ℂ (Module.End.eigenspace ((c • T : H →L[ℂ] H) : H →ₗ[ℂ] H)
        (ν.1 : ℂ)) : ℝ) * ν.1),
    ← tsum_mul_left]
  refine tsum_congr fun μ => ?_
  rw [eigenvalueScaleEquiv_apply]
  rw [show (Module.finrank ℂ (Module.End.eigenspace ((c • T : H →L[ℂ] H) : H →ₗ[ℂ] H)
      ((c * μ.1 : ℝ) : ℂ)) : ℝ) =
      (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)) : ℝ) by
    congr 1
    rw [show ((c * μ.1 : ℝ) : ℂ) = (c : ℂ) * (μ.1 : ℂ) from by push_cast; ring]
    exact congrArg (fun S' : Submodule ℂ H => Module.finrank ℂ S') (eigenspace_smul hc μ.1)]
  ring

end ContinuousLinearMap
