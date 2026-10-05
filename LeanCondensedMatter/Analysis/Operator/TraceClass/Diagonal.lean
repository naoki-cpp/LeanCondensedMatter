import LeanCondensedMatter.Analysis.Operator.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.General

set_option linter.style.header false

/-!
# Trace class for positive diagonal operators

Absolutely summable nonnegative diagonal weights define a positive trace-class operator directly
through the Hilbert-basis diagonal criterion. Spectral consequences belong downstream.
-/

noncomputable section

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A diagonal operator with absolutely summable nonnegative real coefficients is trace class. -/
theorem diagonalOp_isTraceClass (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    IsTraceClass (diagonalOp b (fun i => (a i : ℂ))) := by
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by
    simpa using ha
  let T : H →L[ℂ] H := diagonalOp b (fun i => (a i : ℂ))
  let hpos : T.IsPositive := diagonalOp_isPositive b a ha ha_nonneg
  have hdiag :
      Summable (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i)) := by
    have hpoint :
        (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i)) = a := by
      funext i
      apply Complex.ofReal_injective
      rw [coe_diagonalExpectationValue_right]
      rw [show T (b i) = (a i : ℂ) • b i by
        simpa [T] using diagonalOp_apply_basis b (fun i => (a i : ℂ)) hac i]
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
    rw [hpoint]
    exact Summable.of_norm ha
  apply (isTraceClass_iff_isTraceClassWrt b T).mpr
  have hnonneg : 0 ≤ T := nonneg_iff_isPositive.mpr hpos
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hnonneg
  simpa [IsTraceClassWrt, habs] using hdiag

end HilbertBasis
