import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Basic
import LeanCondensedMatter.Analysis.Operator.Polar

set_option linter.style.header false

/-!
# Trace-norm bounds from Hilbert--Schmidt factorizations

This module adds trace-norm information to the trace-norm-independent factorization layer. It proves
the arithmetic-mean upper bound for every Hilbert--Schmidt factorization and sharpens the basic
controlled factorization to one whose two squared Hilbert--Schmidt norms equal the trace norm.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- For any Hilbert--Schmidt factorization `T = A† B`, the trace norm is bounded by the arithmetic
mean of the squared Hilbert--Schmidt norms. -/
theorem traceNorm_le_half_normSq_add_of_factorization
    {T A B : H →L[ℂ] H} (hT : IsTraceClass T)
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (hfactor : ContinuousLinearMap.adjoint A * B = T) :
    hT.traceNorm ≤ (hA.normSq + hB.normSq) / 2 := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  obtain ⟨U, -, hUright, hUnorm⟩ := exists_leftPolarFactor T
  have hAU : IsHilbertSchmidt (A * U) := isHilbertSchmidt_comp_right hA U
  have hAUnorm_le : hAU.normSq ≤ hA.normSq := by
    have hraw := IsHilbertSchmidt.normSq_comp_right_le hA U
    have hraw' : hAU.normSq ≤ ‖U‖ ^ 2 * hA.normSq := by
      exact (IsHilbertSchmidt.normSq_proof_irrel hAU
        (isHilbertSchmidt_comp_right hA U)) ▸ hraw
    calc
      hAU.normSq ≤ ‖U‖ ^ 2 * hA.normSq := hraw'
      _ ≤ 1 ^ 2 * hA.normSq := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg U) hUnorm 2) hA.normSq_nonneg
      _ = hA.normSq := by rw [one_pow, one_mul]
  have hterm (i : w) :
      inner ℂ (U (d i)) (T (d i)) =
        inner ℂ ((A * U) (d i)) (B (d i)) := by
    calc
      inner ℂ (U (d i)) (T (d i)) =
          inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A * B) (d i)) := by rw [hfactor]
      _ = inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A) (B (d i))) := by
        rw [mul_apply_eq_comp]
      _ = inner ℂ (A (U (d i))) (B (d i)) :=
        ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
      _ = inner ℂ ((A * U) (d i)) (B (d i)) := by rw [mul_apply_eq_comp]
  have hsumInner : Summable (fun i => inner ℂ (U (d i)) (T (d i))) :=
    (hAU.summable_inner_apply hB d).congr fun i => (hterm i).symm
  have hnormSummable : Summable (fun i => ‖inner ℂ (U (d i)) (T (d i))‖) :=
    hsumInner.norm
  have hAUhas : HasSum (fun i => ‖(A * U) (d i)‖ ^ 2) hAU.normSq :=
    hAU.hasSum_norm_sq_apply d
  have hBhas : HasSum (fun i => ‖B (d i)‖ ^ 2) hB.normSq :=
    hB.hasSum_norm_sq_apply d
  have hmajorHas :
      HasSum (fun i => (‖(A * U) (d i)‖ ^ 2 + ‖B (d i)‖ ^ 2) / 2)
        ((hAU.normSq + hB.normSq) / 2) :=
    (hAUhas.add hBhas).div_const 2
  have hpoint_le (i : w) :
      ‖inner ℂ (U (d i)) (T (d i))‖ ≤
        (‖(A * U) (d i)‖ ^ 2 + ‖B (d i)‖ ^ 2) / 2 := by
    rw [hterm]
    exact (norm_inner_le_norm ((A * U) (d i)) (B (d i))).trans (by
      nlinarith [sq_nonneg (‖(A * U) (d i)‖ - ‖B (d i)‖)])
  rw [hT.traceNorm_eq_tsum_norm_inner_left_of_polar U hUright d]
  calc
    (∑' i, ‖inner ℂ (U (d i)) (T (d i))‖) ≤ (hAU.normSq + hB.normSq) / 2 :=
      (hnormSummable.tsum_le_tsum hpoint_le hmajorHas.summable).trans_eq hmajorHas.tsum_eq
    _ ≤ (hA.normSq + hB.normSq) / 2 := by linarith

/-- Every trace-class operator admits a Hilbert--Schmidt factorization whose two squared
Hilbert--Schmidt norms equal the trace norm. -/
theorem exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, ∃ hA : IsHilbertSchmidt A, ∃ hB : IsHilbertSchmidt B,
      ContinuousLinearMap.adjoint A * B = T ∧
      hA.normSq = hT.traceNorm ∧ hB.normSq = hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm_le, hBnorm_le⟩ :=
    hT.exists_hilbertSchmidt_factorization_normSq_le
  have hAnorm_le' : hA.normSq ≤ hT.traceNorm := hAnorm_le
  have hBnorm_le' : hB.normSq ≤ hT.traceNorm := hBnorm_le
  have hlower := hT.traceNorm_le_half_normSq_add_of_factorization hA hB hfactor
  have hAnorm : hA.normSq = hT.traceNorm := by linarith
  have hBnorm : hB.normSq = hT.traceNorm := by linarith
  exact ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩

end IsTraceClass

end ContinuousLinearMap
