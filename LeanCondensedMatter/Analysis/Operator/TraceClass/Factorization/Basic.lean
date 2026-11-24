import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Compact
import LeanCondensedMatter.Analysis.Operator.Polar

set_option linter.style.header false

/-!
# Factorization and compactness of trace-class operators

A trace-class bounded operator factors as `A† B` with Hilbert--Schmidt factors, and conversely
every such product is trace class. The trace norm is bounded by the arithmetic mean of the
squared Hilbert--Schmidt norms of any such factorization. A polar factorization attains this
bound with both squared norms equal to the trace norm. Factorization also implies compactness.
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
  obtain ⟨U, hUleft, -, hUnorm⟩ := exists_leftPolarFactor T
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S := hT
  have hSself : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  let A : H →L[ℂ] H := S * ContinuousLinearMap.adjoint U
  have hA : IsHilbertSchmidt A :=
    isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint U)
  have hAdjA : ContinuousLinearMap.adjoint A = U * S := by
    simpa only [A, ← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star,
      (ContinuousLinearMap.star_eq_adjoint S).trans hSself.adjoint_eq]
  have hfactor : ContinuousLinearMap.adjoint A * S = T := by
    rw [hAdjA, mul_assoc, hSS, hUleft]
  have hSnorm : hS.normSq = hT.traceNorm := rfl
  have hAdjUnorm : ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hUnorm
  have hAnorm_le : hA.normSq ≤ hT.traceNorm := by
    calc
      hA.normSq ≤ hS.normSq :=
        hS.normSq_comp_right_le_of_norm_le_one (ContinuousLinearMap.adjoint U) hAdjUnorm
      _ = hT.traceNorm := hSnorm
  have hlower := hT.traceNorm_le_half_normSq_add_of_factorization hA hS hfactor
  have hAnorm : hA.normSq = hT.traceNorm := by linarith
  exact ⟨A, S, hA, hS, hfactor, hAnorm, hSnorm⟩

end IsTraceClass

/-- A bounded operator is trace class exactly when it admits a factorization `A† B` with
Hilbert--Schmidt factors. -/
theorem isTraceClass_iff_exists_hilbertSchmidt_factorization {T : H →L[ℂ] H} :
    IsTraceClass T ↔
      ∃ A B : H →L[ℂ] H,
        IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ ContinuousLinearMap.adjoint A * B = T := by
  constructor
  · intro hT
    obtain ⟨A, B, hA, hB, hfactor, -, -⟩ :=
      hT.exists_hilbertSchmidt_factorization_normSq_eq_traceNorm
    exact ⟨A, B, hA, hB, hfactor⟩
  · rintro ⟨A, B, hA, hB, hfactor⟩
    obtain ⟨w, d, -⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
    obtain ⟨U, -, hUright, -⟩ := exists_leftPolarFactor T
    have hAU : IsHilbertSchmidt (A * U) := isHilbertSchmidt_comp_right hA U
    have hsum := hAU.summable_inner_apply hB d
    have hpoint (i : w) :
        ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ) =
          inner ℂ ((A * U) (d i)) (B (d i)) := by
      rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp,
        ContinuousLinearMap.adjoint_inner_right U (d i) (T (d i))]
      rw [← hfactor, mul_apply_eq_comp, mul_apply_eq_comp]
      exact ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
    have hcast :
        Summable (fun i =>
          ((diagonalExpectationValue (CFC.abs T) (CFC.abs_nonneg T).isSelfAdjoint (d i) : ℝ) : ℂ)) :=
      hsum.congr fun i => (hpoint i).symm
    apply (isTraceClass_iff_isTraceClassWrt d T).mpr
    rw [IsTraceClassWrt]
    exact Complex.summable_ofReal.mp hcast

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
