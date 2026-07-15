import LeanCondensedMatter.Analysis.TraceClassBasic

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Trace-class compact self-adjoint operators: scalar multiples

Extends `TraceClassBasic.lean`'s `IsTraceClass`/`trace` with compatibility under real scalar
multiplication: `isTraceClass_smul` (trace-class-ness is preserved) and `trace_smul` (the trace
is homogeneous). See `notes/roadmaps/operator-algebra.md` (Track C).
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- A real scalar multiple of a continuous linear map agrees, as an operator, with the complex
scalar multiple by its cast. Useful for bridging lemmas stated for a general (complex) scalar,
such as `IsPositive.smul_of_nonneg`, with the real-scalar convention used elsewhere in this file
(e.g. `trace_smul`, `isTraceClass_smul`). -/
theorem real_smul_eq_complex_smul (r : ℝ) (T : H →L[ℂ] H) : r • T = (r : ℂ) • T := by
  ext x; simp

omit [CompleteSpace H] in
/-- Scaling `T` by a nonzero real `c` scales each eigenvalue by `c` and leaves the
eigenspaces (as submodules) unchanged. -/
theorem eigenspace_smul {c : ℝ} (hc : c ≠ 0) (μ : ℂ) :
    Module.End.eigenspace (((c • T : H →L[ℂ] H)) : H →ₗ[ℂ] H) ((c : ℂ) * μ) =
      Module.End.eigenspace (T : H →ₗ[ℂ] H) μ := by
  have hcv : ∀ v, ((c • T : H →L[ℂ] H) : H →ₗ[ℂ] H) v = (c : ℂ) • ((T : H →ₗ[ℂ] H) v) := fun v => by
    simp
  ext v
  simp only [Module.End.mem_eigenspace_iff, hcv]
  constructor
  · intro h
    have h' : (c : ℂ) • ((T : H →ₗ[ℂ] H) v) = (c : ℂ) • ((μ : ℂ) • v) := by rw [h, mul_smul]
    exact smul_right_injective H (by exact_mod_cast hc) h'
  · intro h
    rw [h, mul_smul]

/-- The reindexing `μ ↦ c * μ` on nonzero eigenvalues, for a nonzero real `c`, as an
`Equiv` on the base index type `{μ : ℝ // μ ≠ 0}`. Named separately (rather than inlined into
`Equiv.sigmaCongr`) so that its `toFun`/`invFun` stay as ordinary function applications instead
of being left as anonymous unreduced lambdas in later goals. -/
noncomputable def eigenvalueScaleEquiv {c : ℝ} (hc : c ≠ 0) :
    { μ : ℝ // μ ≠ 0 } ≃ { μ : ℝ // μ ≠ 0 } where
  toFun a := ⟨c * a.1, mul_ne_zero hc a.2⟩
  invFun a := ⟨a.1 / c, div_ne_zero a.2 hc⟩
  left_inv a := Subtype.ext (mul_div_cancel_left₀ a.1 hc)
  right_inv a := Subtype.ext (show c * (a.1 / c) = a.1 by
    rw [← mul_div_assoc]; exact mul_div_cancel_left₀ a.1 hc)

@[simp] theorem eigenvalueScaleEquiv_apply {c : ℝ} (hc : c ≠ 0) (a : { μ : ℝ // μ ≠ 0 }) :
    ((eigenvalueScaleEquiv hc a : { μ : ℝ // μ ≠ 0 }) : ℝ) = c * a.1 := rfl

omit [CompleteSpace H] in
/-- **Trace-class-ness is preserved under scalar multiplication by a nonzero real.** Unlike
`trace_smul` (which takes `IsTraceClass (c • T)` as an external hypothesis, matching this
project's usual style of not deriving compactness/trace-class facts), this genuinely proves it
from `IsTraceClass T` alone. Proved via `summable_sigma_of_nonneg` (splitting `Summable` over the
dependent `EigenvectorIndex` type into a nonnegativity-only base+fiber criterion), reindexing only
the *base* type `{γ : ℝ // γ ≠ 0}` via `eigenvalueScaleEquiv` — deliberately avoiding a literal
`Equiv (EigenvectorIndex (c • T)) (EigenvectorIndex T)` on the full dependent `Sigma` type (via
`Equiv.sigmaCongr`), which hits a genuine `(kernel) deterministic timeout` here (its
`sigmaCongrLeft` implementation goes through a `cast`, unlike the base-only reindexing used
elsewhere in this file, e.g. `trace_smul`). -/
theorem isTraceClass_smul {c : ℝ} (hc : c ≠ 0) (h : IsTraceClass T) :
    IsTraceClass (c • T) := by
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
/-- **Trace is homogeneous under scalar multiplication by a nonzero real.** -/
theorem trace_smul {c : ℝ} (hc : c ≠ 0) (h : IsTraceClass T)
    (hcT : IsTraceClass (c • T)) :
    trace hcT = c * trace h := by
  change (∑' b : EigenvectorIndex (c • T), b.1.1) = c * ∑' a : EigenvectorIndex T, a.1.1
  rw [tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex_of_isTraceClass hcT),
    tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex_of_isTraceClass h),
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
