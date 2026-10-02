import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm

set_option linter.style.header false

/-!
# Trace norm

This module owns the basis-relative totalized trace-norm series and the canonical real trace norm
for general trace-class bounded operators. The unrestricted series is only a totalized `tsum`;
mathematical trace-norm meaning is attached to an `IsTraceClass` witness.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The totalized trace-norm series evaluated in a chosen Hilbert basis. Outside trace-class
membership, this is only the totalized `tsum` value and is not the trace norm. -/
noncomputable def traceNormSeriesWrt {ι : Type*} (d : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) : ℝ :=
  hilbertSchmidtNormSqSeriesWrt d (CFC.sqrt (CFC.abs T))

/-- The basis-relative trace-norm series is the diagonal series of `|T|`. -/
theorem traceNormSeriesWrt_eq_tsum_diagonalExpectationValue {ι : Type*}
    (d : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNormSeriesWrt d T =
      ∑' i, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) := by
  unfold traceNormSeriesWrt hilbertSchmidtNormSqSeriesWrt
  apply tsum_congr
  intro i
  exact (diagonalExpectationValue_abs_eq_norm_sq_sqrt_abs T (d i)).symm

/-- For a trace-class operator, the trace-norm series has the same value in every Hilbert basis. -/
theorem traceNormSeriesWrt_eq {ι κ : Type*} (d : HilbertBasis ι ℂ H)
    (f : HilbertBasis κ ℂ H) (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceNormSeriesWrt d T = traceNormSeriesWrt f T := by
  unfold traceNormSeriesWrt
  exact hilbertSchmidtNormSqSeriesWrt_eq d f (CFC.sqrt (CFC.abs T)) hT

namespace IsTraceClass

/-- The trace norm of a trace-class operator. -/
noncomputable def traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ℝ :=
  IsHilbertSchmidt.normSq hT

/-- The trace norm is the diagonal trace-norm series in every Hilbert basis. -/
theorem traceNorm_eq_seriesWrt {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm = traceNormSeriesWrt d T := by
  unfold traceNorm traceNormSeriesWrt
  exact IsHilbertSchmidt.normSq_eq_seriesWrt hT d

/-- The trace norm is the diagonal series of `|T|` in every Hilbert basis. -/
theorem traceNorm_eq_tsum_diagonalExpectationValue {T : H →L[ℂ] H}
    (hT : IsTraceClass T) {ι : Type*} (d : HilbertBasis ι ℂ H) :
    hT.traceNorm =
      ∑' i, diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) := by
  rw [hT.traceNorm_eq_seriesWrt d, traceNormSeriesWrt_eq_tsum_diagonalExpectationValue]

/-- The trace norm is independent of the proof of trace-class membership. -/
theorem traceNorm_proof_irrel {T : H →L[ℂ] H} (hT hT' : IsTraceClass T) :
    hT.traceNorm = hT'.traceNorm := by
  exact IsHilbertSchmidt.normSq_proof_irrel hT hT'

/-- The trace norm is nonnegative. -/
theorem traceNorm_nonneg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    0 ≤ hT.traceNorm :=
  IsHilbertSchmidt.normSq_nonneg hT

end IsTraceClass

end ContinuousLinearMap
