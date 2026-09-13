import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Algebraic interaction-picture operators

For an arbitrary basis energy `energy : Config → ℝ`, the interaction picture is diagonal
Heisenberg evolution of an algebraic operator.  The matrix-coefficient formula uses only the finite
support of each algebraic-Fock vector, not finiteness of the whole configuration type.
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

/-- Matrix coefficients acquire the exponential of the free energy difference. No `Fintype`
assumption on `Config` is needed. -/
theorem matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    matrixCoeff (interactionPicture energy V τ) m n =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n := by
  simpa only [interactionPicture] using matrixCoeff_heisenbergEvolve energy τ V m n

/-- Diagonal imaginary-time evolution changes coefficients but does not create new output basis
states in a fixed matrix column. -/
theorem support_interactionPicture_basisState_subset (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (n : Config) :
    (interactionPicture energy V τ (basisState n)).support ⊆
      (V (basisState n)).support := by
  intro m hm
  rw [Finsupp.mem_support_iff] at hm ⊢
  change matrixCoeff (interactionPicture energy V τ) m n ≠ 0 at hm
  change matrixCoeff V m n ≠ 0
  rw [matrixCoeff_interactionPicture] at hm
  intro hzero
  exact hm (by simp [hzero])

/-- Every interaction-picture matrix coefficient is continuous in imaginary time. -/
theorem continuous_matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (interactionPicture energy V τ) m n) := by
  simp only [matrixCoeff_interactionPicture]
  fun_prop

/-- Every interaction-picture matrix coefficient is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (interactionPicture energy V τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_interactionPicture energy V m n).intervalIntegrable a b

end Common
end SecondQuantization
