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

/-- Matrix coefficients acquire the exponential of the free energy difference.  No `Fintype`
assumption on `Config` is needed. -/
theorem matrixCoeff_interactionPicture (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (m n : Config) :
    matrixCoeff (interactionPicture energy V τ) m n =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff V m n := by
  classical
  have hdiag (t : ℝ) (x : AlgebraicFock Config) (c : Config) :
      diagonalEvolution energy t x c =
        Complex.exp ((t * energy c : ℝ) : ℂ) * x c := by
    let eval : AlgebraicFock Config →ₗ[ℂ] ℂ := Finsupp.lapply c
    have hmap : eval.comp (diagonalEvolution energy t) =
        Complex.exp ((t * energy c : ℝ) : ℂ) • eval := by
      apply Finsupp.lhom_ext
      intro a b
      have hb : (Finsupp.single a b : AlgebraicFock Config) = b • basisState a :=
        (Finsupp.smul_single_one a b).symm
      rw [hb, LinearMap.comp_apply, map_smul, diagonalEvolution_basisState, map_smul,
        LinearMap.smul_apply]
      by_cases h : a = c
      · subst a
        simp [eval, basisState, mul_comm]
      · simp [eval, basisState, h]
    have hx := congrArg (fun L => L x) hmap
    simpa only [eval, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      smul_eq_mul] using hx
  rw [interactionPicture, heisenbergEvolve, matrixCoeff, LinearMap.comp_apply,
    LinearMap.comp_apply, diagonalEvolution_basisState, map_smul, map_smul,
    Finsupp.smul_apply, hdiag]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

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
