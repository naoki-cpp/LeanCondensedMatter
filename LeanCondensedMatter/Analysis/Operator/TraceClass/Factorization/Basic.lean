import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.Norm
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.Analysis.Operator.Polar

set_option linter.style.header false

/-!
# Basic Hilbert--Schmidt factorization of trace-class operators

This module owns the trace-norm-independent factorization layer. A trace-class bounded operator
factors as `A† B` with Hilbert--Schmidt factors, and conversely every such product is trace class.
The forward construction also controls both squared Hilbert--Schmidt norms by the squared
Hilbert--Schmidt norm of `sqrt(|T|)`, without depending on the trace-norm API.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsTraceClass

/-- Every trace-class operator factors as `A† B` with Hilbert--Schmidt factors whose squared
Hilbert--Schmidt norms are bounded by the squared Hilbert--Schmidt norm of `sqrt(|T|)`. -/
theorem exists_controlled_hilbertSchmidt_factorization
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, ∃ hA : IsHilbertSchmidt A, ∃ hB : IsHilbertSchmidt B,
      ContinuousLinearMap.adjoint A * B = T ∧
      hA.normSq ≤ IsHilbertSchmidt.normSq hT ∧
      hB.normSq ≤ IsHilbertSchmidt.normSq hT := by
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
  have hSnorm : hS.normSq = IsHilbertSchmidt.normSq hT :=
    IsHilbertSchmidt.normSq_proof_irrel hS hT
  have hAdjUnorm : ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
    exact hUnorm
  have hAnorm_le : hA.normSq ≤ IsHilbertSchmidt.normSq hT := by
    calc
      hA.normSq ≤ ‖ContinuousLinearMap.adjoint U‖ ^ 2 * hS.normSq :=
        IsHilbertSchmidt.normSq_comp_right_le hS (ContinuousLinearMap.adjoint U)
      _ ≤ 1 ^ 2 * hS.normSq := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hAdjUnorm 2) hS.normSq_nonneg
      _ = IsHilbertSchmidt.normSq hT := by rw [one_pow, one_mul, hSnorm]
  exact ⟨A, S, hA, hS, hfactor, hAnorm_le, hSnorm.le⟩

end IsTraceClass

/-- A product `A† B` of Hilbert--Schmidt operators is trace class. -/
private theorem isTraceClass_of_hilbertSchmidt_factorization
    {A B T : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (hfactor : ContinuousLinearMap.adjoint A * B = T) :
    IsTraceClass T := by
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

/-- A bounded operator is trace class exactly when it admits a factorization `A† B` with
Hilbert--Schmidt factors. -/
theorem isTraceClass_iff_exists_hilbertSchmidt_factorization {T : H →L[ℂ] H} :
    IsTraceClass T ↔
      ∃ A B : H →L[ℂ] H,
        IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ ContinuousLinearMap.adjoint A * B = T := by
  constructor
  · intro hT
    obtain ⟨A, B, hA, hB, hfactor, -, -⟩ :=
      hT.exists_controlled_hilbertSchmidt_factorization
    exact ⟨A, B, hA, hB, hfactor⟩
  · rintro ⟨A, B, hA, hB, hfactor⟩
    exact isTraceClass_of_hilbertSchmidt_factorization hA hB hfactor

end ContinuousLinearMap
