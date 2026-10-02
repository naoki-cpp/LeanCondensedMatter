import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm

set_option linter.style.header false

/-!
# Operations on general trace-class operators

Basic closure, trace-linearity, and trace-norm inequalities for the canonical general trace-class
API.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The zero bounded operator is trace class. -/
theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  simp [IsTraceClassWrt]

private theorem diagonalExpectationValue_abs_smul
    (c : ℂ) (T : H →L[ℂ] H) (x : H) :
    diagonalExpectationValue (CFC.abs (c • T)) (CFC.abs_nonneg (c • T)).isSelfAdjoint x =
      ‖c‖ * diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint x := by
  apply Complex.ofReal_injective
  rw [coe_diagonalExpectationValue_right, Complex.ofReal_mul,
    coe_diagonalExpectationValue_right, CFC.abs_smul]
  simp [RCLike.real_smul_eq_coe_smul, inner_smul_right]

/-- Trace-class membership is closed under complex scalar multiplication. -/
theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  apply IsTraceClass.of_isTraceClassWrt (d := d)
  rw [IsTraceClassWrt]
  have hsum := hT.isTraceClassWrt d
  rw [IsTraceClassWrt] at hsum
  exact (hsum.mul_left ‖c‖).congr fun i => (diagonalExpectationValue_abs_smul c T (d i)).symm

/-- Trace-class membership is closed under negation. -/
theorem IsTraceClass.neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (-T) := by
  simpa only [neg_one_smul] using hT.smul (-1 : ℂ)

namespace IsTraceClass

/-- The zero operator has trace norm zero. -/
@[simp]
theorem traceNorm_zero :
    (isTraceClass_zero (H := H)).traceNorm = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isTraceClass_zero (H := H)).traceNorm_eq_tsum_diagonalExpectationValue d]
  simp

/-- Scalar multiplication scales the trace norm by the scalar norm. -/
theorem traceNorm_smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    (hT.smul c).traceNorm = ‖c‖ * hT.traceNorm := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(hT.smul c).traceNorm_eq_tsum_diagonalExpectationValue d,
    hT.traceNorm_eq_tsum_diagonalExpectationValue d]
  simp_rw [diagonalExpectationValue_abs_smul c T]
  rw [tsum_mul_left]

/-- Negation preserves the trace norm. -/
@[simp]
theorem traceNorm_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.neg.traceNorm = hT.traceNorm := by
  rw [show -T = (-1 : ℂ) • T by simp, traceNorm_proof_irrel hT.neg (hT.smul (-1 : ℂ)),
    hT.traceNorm_smul]
  simp

/-- The zero operator has trace zero. -/
@[simp]
theorem trace_zero :
    (isTraceClass_zero (H := H)).trace = 0 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(isTraceClass_zero (H := H)).trace_eq_seriesWrt d]
  simp [traceSeriesWrt]

/-- The trace is complex-linear under scalar multiplication. -/
theorem trace_smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    (hT.smul c).trace = c * hT.trace := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  rw [(hT.smul c).trace_eq_seriesWrt d, hT.trace_eq_seriesWrt d]
  unfold traceSeriesWrt
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  simp [inner_smul_right]

/-- The trace changes sign under negation. -/
@[simp]
theorem trace_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    hT.neg.trace = -hT.trace := by
  rw [show -T = (-1 : ℂ) • T by simp, trace_proof_irrel hT.neg (hT.smul (-1 : ℂ)),
    hT.trace_smul]
  simp

end IsTraceClass

end ContinuousLinearMap
