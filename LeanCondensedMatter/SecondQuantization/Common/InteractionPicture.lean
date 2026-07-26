import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution

set_option linter.style.header false

/-!
# Algebraic interaction-picture operators

For an arbitrary basis energy `energy : Config → ℝ`, the interaction picture is diagonal
Heisenberg evolution of an algebraic operator. Its matrix coefficients acquire the exponential of
the basis-energy difference. This construction is independent of particle statistics.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The interaction-picture operator for a basis-diagonal free energy. -/
noncomputable def interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  heisenbergEvolve energy τ V

/-- At zero imaginary time, the interaction picture is the original operator. -/
@[simp]
theorem interactionPicture_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    interactionPicture energy V 0 = V :=
  heisenbergEvolve_zero energy V

/-- Matrix coefficients acquire the exponential of the free energy difference. -/
theorem matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    matrixCoeff (interactionPicture energy V τ) m n =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n :=
  matrixCoeff_heisenbergEvolve energy τ V m n

/-- Every matrix coefficient of an interaction-picture operator is continuous in imaginary time. -/
theorem continuous_matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (interactionPicture energy V τ) m n) := by
  simp only [matrixCoeff_interactionPicture]
  fun_prop

/-- Every matrix coefficient of an interaction-picture operator is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (interactionPicture energy V τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_interactionPicture energy V m n).intervalIntegrable a b

end Common
end SecondQuantization
