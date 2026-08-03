import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationTraceClass
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option linter.style.header false

/-!
# Order and reality properties of density-operator expectations

A symmetric bounded observable has a real expectation in every trace-class density state. A
positive bounded observable additionally has a nonnegative expectation. These lemmas complement
the complex-linear and contractive expectation API with the reality and order facts used for
observables, probabilities, and positive operators.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem inner_apply_im_eq_zero_of_isSymmetric
    {A : H →L[ℂ] H} (hA : (A : H →ₗ[ℂ] H).IsSymmetric) (x : H) :
    (inner ℂ x (A x) : ℂ).im = 0 := by
  simpa using hA.im_inner_self_apply x

/-- The expectation of a symmetric bounded observable has zero imaginary part. -/
theorem DensityOperator.expectation_im_eq_zero_of_isSymmetric
    (ρ : DensityOperator H) {A : H →L[ℂ] H}
    (hA : (A : H →ₗ[ℂ] H).IsSymmetric) :
    (ρ.expectation A).im = 0 := by
  rw [ρ.expectation_apply, Complex.im_tsum (ρ.summable_expectation_term A)]
  calc
    (∑' a : EigenvectorIndex ρ.op,
        ((a.1.1 : ℂ) *
          (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
            (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)).im) =
        ∑' _a : EigenvectorIndex ρ.op, (0 : ℝ) := by
      apply tsum_congr
      intro a
      simp [Complex.mul_im, inner_apply_im_eq_zero_of_isSymmetric hA]
    _ = 0 := tsum_zero

/-- The expectation of a symmetric bounded observable is a self-adjoint complex scalar,
equivalently a real number embedded in `ℂ`. -/
theorem DensityOperator.expectation_isSelfAdjoint_of_isSymmetric
    (ρ : DensityOperator H) {A : H →L[ℂ] H}
    (hA : (A : H →ₗ[ℂ] H).IsSymmetric) :
    IsSelfAdjoint (ρ.expectation A) :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).mp
    (ρ.expectation_im_eq_zero_of_isSymmetric hA)

omit [CompleteSpace H] in
private theorem inner_apply_im_eq_zero_of_isPositive
    {A : H →L[ℂ] H} (hA : A.IsPositive) (x : H) :
    (inner ℂ x (A x) : ℂ).im = 0 := by
  have hreal := Complex.eq_coe_norm_of_nonneg (hA.inner_nonneg_right x)
  exact congrArg Complex.im hreal

/-- The expectation of a positive observable has zero imaginary part. -/
theorem DensityOperator.expectation_im_eq_zero_of_isPositive
    (ρ : DensityOperator H) {A : H →L[ℂ] H} (hA : A.IsPositive) :
    (ρ.expectation A).im = 0 := by
  rw [ρ.expectation_apply, Complex.im_tsum (ρ.summable_expectation_term A)]
  calc
    (∑' a : EigenvectorIndex ρ.op,
        ((a.1.1 : ℂ) *
          (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
            (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)).im) =
        ∑' _a : EigenvectorIndex ρ.op, (0 : ℝ) := by
      apply tsum_congr
      intro a
      simp [Complex.mul_im, inner_apply_im_eq_zero_of_isPositive hA]
    _ = 0 := tsum_zero

/-- The expectation of a positive observable is a self-adjoint complex scalar, equivalently a real
number embedded in `ℂ`. -/
theorem DensityOperator.expectation_isSelfAdjoint_of_isPositive
    (ρ : DensityOperator H) {A : H →L[ℂ] H} (hA : A.IsPositive) :
    IsSelfAdjoint (ρ.expectation A) :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).mp
    (ρ.expectation_im_eq_zero_of_isPositive hA)

/-- The real part of the expectation of a positive observable is nonnegative. -/
theorem DensityOperator.expectation_re_nonneg_of_isPositive
    (ρ : DensityOperator H) {A : H →L[ℂ] H} (hA : A.IsPositive) :
    0 ≤ (ρ.expectation A).re := by
  rw [ρ.expectation_apply, Complex.re_tsum (ρ.summable_expectation_term A)]
  apply tsum_nonneg
  intro a
  simpa [Complex.mul_re] using
    mul_nonneg (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)
      (hA.re_inner_nonneg_right (eigenvectorFamily ρ.spectralTraceClass.compact a))

/-- The expectation functional sends positive bounded observables to nonnegative complex scalars. -/
theorem DensityOperator.expectation_nonneg_of_isPositive
    (ρ : DensityOperator H) {A : H →L[ℂ] H} (hA : A.IsPositive) :
    0 ≤ ρ.expectation A := by
  exact (Complex.re_nonneg_iff_nonneg
    (ρ.expectation_isSelfAdjoint_of_isPositive hA)).mp
      (ρ.expectation_re_nonneg_of_isPositive hA)

end QuantumTheory.TraceClass
