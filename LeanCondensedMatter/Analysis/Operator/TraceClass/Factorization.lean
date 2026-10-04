import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.Analysis.Operator.Polar

set_option linter.style.header false

/-!
# Hilbert--Schmidt factorization of trace-class operators

A bounded operator is trace class exactly when it factors as `A† B` with Hilbert--Schmidt
operators `A` and `B`. This characterization is independent of the trace value and is the
shared structural input for compactness, ideal closure, and trace convergence.
-/

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every trace-class operator factors as `A† B` with Hilbert--Schmidt factors. -/
private theorem exists_hilbertSchmidt_factorization_of_isTraceClass
    {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H,
      IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ ContinuousLinearMap.adjoint A * B = T := by
  obtain ⟨U, hU, -, -⟩ := exists_leftPolarFactor T
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S := hT
  have hSself : IsSelfAdjoint S := (CFC.sqrt_nonneg (CFC.abs T)).isSelfAdjoint
  have hSS : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  let A : H →L[ℂ] H := S * ContinuousLinearMap.adjoint U
  have hA : IsHilbertSchmidt A :=
    isHilbertSchmidt_comp_right hS (ContinuousLinearMap.adjoint U)
  have hAdjA : ContinuousLinearMap.adjoint A = U * S := by
    rw [show ContinuousLinearMap.adjoint A = star A from
      (ContinuousLinearMap.star_eq_adjoint A).symm]
    dsimp [A]
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.star_eq_adjoint,
      hSself.adjoint_eq]
  refine ⟨A, S, hA, hS, ?_⟩
  rw [hAdjA, mul_assoc, hSS, hU]

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
    rw [coe_diagonalExpectationValue_right, ← hUright, mul_apply_eq_comp]
    calc
      inner ℂ (d i) ((ContinuousLinearMap.adjoint U) (T (d i))) =
          inner ℂ (U (d i)) (T (d i)) :=
        ContinuousLinearMap.adjoint_inner_right U (d i) (T (d i))
      _ = inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A * B) (d i)) := by
        rw [hfactor]
      _ = inner ℂ (U (d i)) ((ContinuousLinearMap.adjoint A) (B (d i))) := by
        rw [mul_apply_eq_comp]
      _ = inner ℂ (A (U (d i))) (B (d i)) :=
        ContinuousLinearMap.adjoint_inner_right A (U (d i)) (B (d i))
      _ = inner ℂ ((A * U) (d i)) (B (d i)) := by
        rw [mul_apply_eq_comp]
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
  · exact exists_hilbertSchmidt_factorization_of_isTraceClass
  · rintro ⟨A, B, hA, hB, hfactor⟩
    exact isTraceClass_of_hilbertSchmidt_factorization hA hB hfactor

end ContinuousLinearMap
