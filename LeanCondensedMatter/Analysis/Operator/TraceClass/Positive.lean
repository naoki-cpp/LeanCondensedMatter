import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.TraceClass.Compact
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Basic

set_option linter.style.header false

/-!
# Positive trace-class operators

For a positive trace-class operator, the lossless real trace agrees with the trace norm and
is strictly positive when the operator is nonzero.
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

/-- A nonzero positive trace-class operator has strictly positive lossless real trace. -/
theorem realTrace_pos {T : H →L[ℂ] H}
    (hT : IsTraceClass T) (hpos : T.IsPositive) (hne : T ≠ 0) :
    0 < hT.realTrace hpos.isSelfAdjoint := by
  classical
  let hc := hT.isCompact
  have he := orthonormal_eigenvectorFamily hc hpos.isSelfAdjoint.isSymmetric
  have hnonempty : Nonempty (EigenvectorIndex T) := by
    by_contra hidx
    haveI : IsEmpty (EigenvectorIndex T) := ⟨fun a => hidx ⟨a⟩⟩
    apply hne
    ext x
    have hsum := hasSum_eigenvectorFamily hc hpos.isSelfAdjoint.isSymmetric x
    simpa using hsum.tsum_eq.symm
  let a : EigenvectorIndex T := Classical.choice hnonempty
  have hapos : 0 < a.1.1 :=
    lt_of_le_of_ne (eigenvalue_nonneg_of_isPositive hpos.toLinearMap a) (Ne.symm a.1.2)
  have hdiag : diagonalExpectationValue T hpos.isSelfAdjoint
      (eigenvectorFamily hc a) = a.1.1 := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    change inner ℂ (eigenvectorFamily hc a)
      ((T : H →ₗ[ℂ] H) (eigenvectorFamily hc a)) = _
    rw [apply_eigenvectorFamily, inner_smul_right, inner_self_eq_norm_sq_to_K, he.1 a]
    simp
  have hbound := hT.sum_diagonalExpectationValue_le_traceNorm hpos he
  have hle := hbound.1.le_tsum a
    (fun b _ => diagonalExpectationValue_nonneg T hpos (eigenvectorFamily hc b))
  rw [hdiag] at hle
  rw [← hT.traceNorm_eq_realTrace hpos]
  exact hapos.trans_le (hle.trans hbound.2)

end IsTraceClass

end ContinuousLinearMap
