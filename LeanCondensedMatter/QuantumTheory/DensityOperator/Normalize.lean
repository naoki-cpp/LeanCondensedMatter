import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Scalar
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Normalization of positive trace-class operators

A nonzero positive spectral-trace-class operator has strictly positive trace, so it can be
normalized canonically to a density operator. This construction is independent of any Gibbs or
spectral-data representation.
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
  have hscaledPos : (r • T).IsPositive := by
    rw [show r • T = (r : ℂ) • T by ext x; simp]
    exact hpos.smul_of_nonneg (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZpos.le))
  let hscaledTrace : SpectralTraceClass (r • T) := htrace.smul r
  exact {
    op := r • T
    pos := hscaledPos
    spectralTraceClass := hscaledTrace
    trace_eq_one := by
      rw [hscaledTrace.isTraceClass.trace_eq_spectralTrace
        hscaledTrace.compact hscaledTrace.isSelfAdjoint]
      have hspectral : spectralTrace (r • T) = 1 := by
        rw [spectralTrace_smul r htrace.summable]
        dsimp [r, Z]
        exact inv_mul_cancel₀ (ne_of_gt hZpos)
      exact_mod_cast hspectral
  }

@[simp]
theorem normalizePositive_op
    (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (htrace : SpectralTraceClass T) (hne : T ≠ 0) :
    (normalizePositive T hpos htrace hne).op = (spectralTrace T)⁻¹ • T := by
  rfl

end DensityOperator

end QuantumTheory
