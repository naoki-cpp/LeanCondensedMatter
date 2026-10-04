import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Normalization of positive trace-class operators

A nonzero positive self-adjoint trace-class operator has strictly positive spectral trace, so it can
be normalized canonically to a density operator. The normalization proof uses the general complex
trace and its scalar linearity; no scalar reindexing of spectral eigenspaces is required.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DensityOperator

/-- Normalize a nonzero positive spectral-trace-class operator to a density operator. -/
noncomputable def normalizePositive
    (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (htrace : SpectralTraceClass T) (hne : T ≠ 0) : DensityOperator H := by
  let Z : ℝ := spectralTrace T
  let r : ℝ := Z⁻¹
  have hZpos : 0 < Z := by
    simpa [Z] using htrace.spectralTrace_pos hpos hne
  have hscaledPos : ((r : ℂ) • T).IsPositive :=
    hpos.smul_of_nonneg (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZpos.le))
  let hscaledTrace : IsTraceClass ((r : ℂ) • T) :=
    htrace.isTraceClass.smul (r : ℂ)
  exact {
    op := (r : ℂ) • T
    pos := hscaledPos
    isTraceClass := hscaledTrace
    trace_eq_one := by
      dsimp [hscaledTrace]
      rw [htrace.isTraceClass.trace_smul,
        htrace.isTraceClass.trace_eq_spectralTrace htrace.isSelfAdjoint]
      dsimp [r, Z]
      exact_mod_cast inv_mul_cancel₀ (ne_of_gt hZpos)
  }

@[simp]
theorem normalizePositive_op
    (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (htrace : SpectralTraceClass T) (hne : T ≠ 0) :
    (normalizePositive T hpos htrace hne).op = (spectralTrace T)⁻¹ • T := by
  change (((spectralTrace T)⁻¹ : ℝ) : ℂ) • T = (spectralTrace T)⁻¹ • T
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]

end DensityOperator

end QuantumTheory
