import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Positive
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Normalization of positive trace-class operators

A nonzero positive trace-class operator has strictly positive lossless real trace, so it can
be normalized canonically to a density operator. The normalization proof uses the general complex
trace and its scalar linearity; no scalar reindexing of spectral eigenspaces is required.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DensityOperator

/-- Normalize a nonzero positive trace-class operator to a density operator. -/
noncomputable def normalizePositive
    (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (htrace : IsTraceClass T) (hne : T ≠ 0) : DensityOperator H := by
  let Z : ℝ := htrace.realTrace hpos.isSelfAdjoint
  let r : ℝ := Z⁻¹
  have hZpos : 0 < Z := by
    simpa [Z] using htrace.realTrace_pos hpos hne
  have hscaledPos : ((r : ℂ) • T).IsPositive :=
    hpos.smul_of_nonneg (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZpos.le))
  let hscaledTrace : IsTraceClass ((r : ℂ) • T) :=
    htrace.smul (r : ℂ)
  exact {
    op := (r : ℂ) • T
    pos := hscaledPos
    isTraceClass := hscaledTrace
    trace_eq_one := by
      dsimp [hscaledTrace]
      rw [htrace.trace_smul,
        ← htrace.coe_realTrace hpos.isSelfAdjoint]
      dsimp [r, Z]
      exact_mod_cast inv_mul_cancel₀ (ne_of_gt hZpos)
  }

@[simp]
theorem normalizePositive_op
    (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (htrace : IsTraceClass T) (hne : T ≠ 0) :
    (normalizePositive T hpos htrace hne).op = (htrace.realTrace hpos.isSelfAdjoint)⁻¹ • T := by
  change (((htrace.realTrace hpos.isSelfAdjoint)⁻¹ : ℝ) : ℂ) • T =
    (htrace.realTrace hpos.isSelfAdjoint)⁻¹ • T
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end DensityOperator

end QuantumTheory
