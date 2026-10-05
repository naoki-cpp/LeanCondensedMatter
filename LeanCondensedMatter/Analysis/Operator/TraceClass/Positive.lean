import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace

set_option linter.style.header false

/-!
# Positive trace-class operators

For a positive trace-class operator, the lossless real trace agrees with the trace norm.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- The trace norm of a positive trace-class operator equals its lossless real trace. -/
theorem traceNorm_eq_realTrace {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) :
    hT.traceNorm = hT.realTrace hpos.isSelfAdjoint := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  exact
    (hT.hasSum_diagonalExpectationValue_eq_traceNorm hpos d).unique
      (hT.hasSum_realTrace hpos.isSelfAdjoint d)

end IsTraceClass

end ContinuousLinearMap
