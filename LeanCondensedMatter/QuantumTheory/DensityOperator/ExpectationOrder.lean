import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option linter.style.header false

/-!
# Order and reality properties of density-operator expectations

A symmetric bounded observable has a real expectation in every density state. A positive bounded
observable additionally has a nonnegative expectation.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation of a symmetric bounded observable has zero imaginary part. -/
theorem DensityOperator.expectation_im_eq_zero_of_isSymmetric
    (ρ : DensityOperator H) {A : H →L[ℂ] H}
    (hA : (A : H →ₗ[ℂ] H).IsSymmetric) :
    (ρ.expectation A).im = 0 := by
  rw [ρ.expectation_eq_spectral_tsum, Complex.im_tsum (ρ.summable_expectation_term A)]
  calc
    (∑' a : EigenvectorIndex ρ.op,
        ((a.1.1 : ℂ) *
          (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
            (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ)).im) =
        ∑' _a : EigenvectorIndex ρ.op, (0 : ℝ) := by
      apply tsum_congr
      intro a
      have him :
          (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
            (A (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ).im = 0 := by
        simpa using
          hA.im_inner_self_apply (eigenvectorFamily ρ.spectralTraceClass.compact a)
      simp [Complex.mul_im, him]
    _ = 0 := tsum_zero

/-- The expectation of a symmetric bounded observable is a self-adjoint complex scalar. -/
theorem DensityOperator.expectation_isSelfAdjoint_of_isSymmetric
    (ρ : DensityOperator H) {A : H →L[ℂ] H}
    (hA : (A : H →ₗ[ℂ] H).IsSymmetric) :
    IsSelfAdjoint (ρ.expectation A) :=
  (Complex.im_eq_zero_iff_isSelfAdjoint _).mp
    (ρ.expectation_im_eq_zero_of_isSymmetric hA)

/-- The real part of the expectation of a positive observable is nonnegative. -/
theorem DensityOperator.expectation_re_nonneg_of_isPositive
    (ρ : DensityOperator H) {A : H →L[ℂ] H} (hA : A.IsPositive) :
    0 ≤ (ρ.expectation A).re := by
  rw [ρ.expectation_eq_spectral_tsum, Complex.re_tsum (ρ.summable_expectation_term A)]
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
    (ρ.expectation_isSelfAdjoint_of_isSymmetric hA.isSelfAdjoint.isSymmetric)).mp
      (ρ.expectation_re_nonneg_of_isPositive hA)

end QuantumTheory
