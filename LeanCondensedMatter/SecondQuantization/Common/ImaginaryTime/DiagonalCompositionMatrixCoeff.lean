import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Matrix coefficients after diagonal left composition

A diagonal free evolution rescales each output coordinate independently. This elementary formula is
useful below both perturbation theory and thermal summability, so it belongs in the Common
imaginary-time layer rather than either downstream consumer.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- Left composition by a diagonal evolution rescales a matrix coefficient by the output
configuration's exponential weight. -/
theorem matrixCoeff_diagonalEvolution_comp
    (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (m n : Config) :
    matrixCoeff ((diagonalEvolution energy τ).comp A) m n =
      Complex.exp ((τ * energy m : ℝ) : ℂ) * matrixCoeff A m n := by
  rw [matrixCoeff, LinearMap.comp_apply, diagonalEvolution, diagonalOperator_apply]
  rfl

end
end Common
end SecondQuantization
