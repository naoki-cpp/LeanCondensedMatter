import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationTraceClass
import Mathlib.Analysis.InnerProductSpace.Positive

set_option linter.style.header false

/-!
# Order properties of density-operator expectations

A positive bounded observable has a real, nonnegative expectation in every trace-class density
state.  These lemmas complement the complex-linear and contractive expectation API with the
order-theoretic facts used for probabilities and positive observables.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
