import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import Mathlib.Analysis.InnerProductSpace.l2Space
import LeanCondensedMatter.Analysis.Operator.Diagonal

set_option linter.style.header false

/-!
# Positive trace-class operators

For a positive trace-class operator, the lossless real trace agrees with the trace norm and
is strictly positive when the operator is nonzero. Positive diagonal operators with absolutely
summable weights are trace class through the Hilbert-basis diagonal criterion.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive rank-one operator is trace class, without any normalization of its vector. -/
theorem isTraceClass_rankOne_self (x : H) :
    IsTraceClass (InnerProductSpace.rankOne ℂ x x) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let T : H →L[ℂ] H := InnerProductSpace.rankOne ℂ x x
  have hpos : T.IsPositive := InnerProductSpace.isPositive_rankOne_self x
  have hdiag (i : w) :
      diagonalExpectationValue T hpos.isSelfAdjoint (b i) =
        ‖(inner ℂ x (b i) : ℂ)‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    simp only [T, InnerProductSpace.rankOne_apply, inner_smul_right]
    rw [show (inner ℂ (b i) x : ℂ) = starRingEnd ℂ (inner ℂ x (b i)) from
      (inner_conj_symm (b i) x).symm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply (isTraceClass_iff_isTraceClassWrt b T).mpr
  have habs : CFC.abs T = T :=
    CFC.abs_of_nonneg T (nonneg_iff_isPositive.mpr hpos)
  have hsum : HasSum (fun i => ‖(inner ℂ x (b i) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two,
      b.repr_apply_apply, b.repr.norm_map, norm_inner_symm] using
      (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))
  simpa only [IsTraceClassWrt, habs] using
    (hsum.summable.congr fun i => (hdiag i).symm)

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
  rw [← hT.traceNorm_eq_realTrace hpos]
  have habs : CFC.abs T = T :=
    CFC.abs_of_nonneg T (nonneg_iff_isPositive.mpr hpos)
  have hsne : CFC.sqrt (CFC.abs T) ≠ 0 := by
    intro hz
    have hsq := CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
    rw [hz, zero_mul, habs] at hsq
    exact hne hsq.symm
  exact IsHilbertSchmidt.normSq_pos hT hsne

end IsTraceClass

end ContinuousLinearMap

/-! ## Positive diagonal operators -/

namespace HilbertBasis

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A diagonal operator with absolutely summable nonnegative real coefficients is trace class. -/
theorem diagonalOp_isTraceClass (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    IsTraceClass (diagonalOp b (fun i => (a i : ℂ))) := by
  let T : H →L[ℂ] H := diagonalOp b (fun i => (a i : ℂ))
  let hpos : T.IsPositive := diagonalOp_isPositive b a ha ha_nonneg
  have hdiag :
      Summable (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i)) := by
    have hpoint :
        (fun i => diagonalExpectationValue T hpos.isSelfAdjoint (b i)) = a := by
      funext i
      simpa [T] using diagonalExpectationValue_diagonalOp b a ha ha_nonneg i
    rw [hpoint]
    exact Summable.of_norm ha
  apply (isTraceClass_iff_isTraceClassWrt b T).mpr
  have hnonneg : 0 ≤ T := nonneg_iff_isPositive.mpr hpos
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hnonneg
  simpa [IsTraceClassWrt, habs] using hdiag

end HilbertBasis
