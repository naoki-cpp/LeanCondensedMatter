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
  have hAUnorm_le : hAU.normSq ≤ hA.normSq :=
    hA.normSq_comp_right_le_of_norm_le_one U hUnorm
  have hterm (i : w) :
      inner ℂ (U (d i)) (T (d i)) =
        inner ℂ ((A * U) (d i)) (B (d i)) := by
    rw [← hfactor, mul_apply_eq_comp, mul_apply_eq_comp]
    exact ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
  have hpair := hAU.summable_norm_inner_apply_and_tsum_le hB d
  rw [hT.traceNorm_eq_tsum_norm_inner_left_of_polar U hUright d]
  calc
    (∑' i, ‖inner ℂ (U (d i)) (T (d i))‖) =
        ∑' i, ‖inner ℂ ((A * U) (d i)) (B (d i))‖ := by
      apply tsum_congr
      intro i
      rw [hterm]
    _ ≤ (hAU.normSq + hB.normSq) / 2 := hpair.2
    _ ≤ (hA.normSq + hB.normSq) / 2 := by linarith

/-- Every trace-class operator admits a Hilbert--Schmidt factorization whose two squared
Hilbert--Schmidt norms equal the trace norm. -/
theorem exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, ∃ hA : IsHilbertSchmidt A, ∃ hB : IsHilbertSchmidt B,
      ContinuousLinearMap.adjoint A * B = T ∧
      hA.normSq = hT.traceNorm ∧ hB.normSq = hT.traceNorm := by
  obtain ⟨A, B, hA, hB, hfactor, hAnorm_le, hBnorm_le⟩ :=
    hT.exists_controlled_hilbertSchmidt_factorization
  have hAnorm_le' : hA.normSq ≤ hT.traceNorm := hAnorm_le
  have hBnorm_le' : hB.normSq ≤ hT.traceNorm := hBnorm_le
  have hlower := hT.traceNorm_le_half_normSq_add_of_factorization hA hB hfactor
  have hAnorm : hA.normSq = hT.traceNorm := by linarith
  have hBnorm : hB.normSq = hT.traceNorm := by linarith
  exact ⟨A, B, hA, hB, hfactor, hAnorm, hBnorm⟩

end IsTraceClass

end ContinuousLinearMap
