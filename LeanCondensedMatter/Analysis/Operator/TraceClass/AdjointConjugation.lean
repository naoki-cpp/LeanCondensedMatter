import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
import LeanCondensedMatter.Analysis.Operator.TraceClass.Cyclicity

set_option linter.style.header false

/-!
# Adjoint conjugation of trace-class operators

General trace-class membership is preserved by bounded adjoint conjugation `T ↦ U T U†`.
If `U† U = 1`, cyclicity gives trace invariance; surjectivity of `U` is not needed.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- Bounded adjoint conjugation preserves trace-class membership. -/
theorem adjointConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H) :
    IsTraceClass (ContinuousLinearMap.adjointConjugate U T) := by
  simpa [ContinuousLinearMap.adjointConjugate, mul_assoc] using
    (hT.comp_left U).comp_right (star U)

/-- If `U† U = 1`, then `Tr(U T U†) = Tr(T)` for every trace-class `T`. -/
theorem trace_adjointConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) :
    (hT.adjointConjugate U).trace = hT.trace := by
  simpa only [ContinuousLinearMap.adjointConjugate, ← mul_assoc, hleft, one_mul] using
    (hT.comp_left U).trace_comp_comm (star U)

end IsTraceClass

end ContinuousLinearMap
