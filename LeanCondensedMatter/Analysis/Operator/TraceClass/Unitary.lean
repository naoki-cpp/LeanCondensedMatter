import LeanCondensedMatter.Analysis.Operator.TraceClass.Cyclicity
import LeanCondensedMatter.Analysis.Operator.Unitary

set_option linter.style.header false

/-!
# Unitary conjugation of trace-class operators

General trace-class membership is preserved by bounded adjoint conjugation `T ↦ U T U†`.
If `U† U = 1`, cyclicity gives trace invariance. Surjectivity of `U` is not needed for the
trace identity.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- Bounded adjoint conjugation preserves trace-class membership. -/
theorem unitaryConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H) :
    IsTraceClass (ContinuousLinearMap.unitaryConjugate U T) := by
  simpa [ContinuousLinearMap.unitaryConjugate, mul_assoc] using
    (hT.comp_left U).comp_right (star U)

/-- If `U† U = 1`, then `Tr(U T U†) = Tr(T)` for every trace-class `T`. -/
theorem trace_unitaryConjugate {T : H →L[ℂ] H} (hT : IsTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) :
    (hT.unitaryConjugate U).trace = hT.trace := by
  simpa only [ContinuousLinearMap.unitaryConjugate, ← mul_assoc, hleft, one_mul] using
    (hT.comp_left U).trace_comp_comm (star U)

end IsTraceClass

end ContinuousLinearMap
