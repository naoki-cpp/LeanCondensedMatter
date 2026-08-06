import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Matrix-coefficient Dyson boundary for infinite configuration spaces

The finite operator integral reconstructs an algebraic-Fock operator by summing over every output
basis state, so it requires `[Fintype Config]`.  That reconstruction is not available for bosonic
occupation configurations, which remain infinite even when the mode type is finite.

This file keeps only the scalar matrix coefficient of the first Dyson term.  The scalar interval
integral is meaningful for an arbitrary configuration type and does not assert that the resulting
family of coefficients reconstructs an algebraic operator, bounded operator, or quadratic form.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The first interaction-picture Dyson coefficient at a fixed pair of basis configurations.

This is the safe infinite-configuration replacement for the matrix coefficient of
`dysonCoeff energy V 1 τ`: no operator-valued integral is reconstructed. -/
noncomputable def firstDysonMatrixCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) : ℂ :=
  - ∫ σ in (0 : ℝ)..τ, matrixCoeff (interactionPicture energy V σ) m n

@[simp]
theorem firstDysonMatrixCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    firstDysonMatrixCoeff energy V 0 m n = 0 := by
  simp [firstDysonMatrixCoeff]

/-- The first coefficient is the integral of the explicit interaction-picture phase times the
original matrix coefficient. -/
theorem firstDysonMatrixCoeff_eq_phase_integral (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    firstDysonMatrixCoeff energy V τ m n =
      - ∫ σ in (0 : ℝ)..τ,
          Complex.exp ((σ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n := by
  unfold firstDysonMatrixCoeff
  apply congrArg Neg.neg
  exact intervalIntegral.integral_congr fun σ _ =>
    matrixCoeff_interactionPicture energy V σ m n

/-- Every first-order Dyson matrix coefficient is continuous in the upper imaginary-time bound. -/
theorem continuous_firstDysonMatrixCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    Continuous (fun τ : ℝ => firstDysonMatrixCoeff energy V τ m n) := by
  unfold firstDysonMatrixCoeff
  exact (intervalIntegral.continuous_primitive
    (fun a b => (intervalIntegrable_matrixCoeff_interactionPicture energy V m n a b)) 0).neg

end Common
end SecondQuantization
