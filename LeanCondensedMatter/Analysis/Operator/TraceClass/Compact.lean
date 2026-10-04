import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Compact
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace

set_option linter.style.header false

/-!
# Compactness of trace-class operators

Every trace-class operator is compact. The proof uses the Hilbert--Schmidt factorization
`T = A† B`: the Hilbert--Schmidt factor `B` is compact, and bounded left composition preserves
compactness.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- Every trace-class operator is compact. -/
theorem isCompact {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T := by
  obtain ⟨A, B, -, hB, hfactor⟩ :=
    (isTraceClass_iff_exists_hilbertSchmidt_factorization (T := T)).mp hT
  rw [← hfactor]
  change IsCompactOperator
    (⇑(ContinuousLinearMap.adjoint A) ∘ ⇑B)
  exact hB.isCompact.clm_comp (ContinuousLinearMap.adjoint A)

end IsTraceClass

end ContinuousLinearMap
