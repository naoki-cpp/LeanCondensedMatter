import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Matrix coefficients after diagonal left composition

A diagonal free evolution rescales each output coordinate independently.  This elementary formula is
useful below both perturbation theory and thermal summability, so it belongs in the Common
imaginary-time layer rather than either downstream consumer.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- Coordinate formula for diagonal evolution on an arbitrary algebraic-Fock vector. -/
private theorem diagonalEvolution_apply_coord
    (energy : Config → ℝ) (τ : ℝ) (x : AlgebraicFock Config) (m : Config) :
    diagonalEvolution energy τ x m =
      Complex.exp ((τ * energy m : ℝ) : ℂ) * x m := by
  let eval : AlgebraicFock Config →ₗ[ℂ] ℂ := Finsupp.lapply m
  have hmap : eval.comp (diagonalEvolution energy τ) =
      Complex.exp ((τ * energy m : ℝ) : ℂ) • eval := by
    apply Finsupp.lhom_ext
    intro a b
    have hb : (Finsupp.single a b : AlgebraicFock Config) = b • basisState a :=
      (Finsupp.smul_single_one a b).symm
    rw [hb, LinearMap.comp_apply, map_smul, diagonalEvolution_basisState]
    simp only [map_smul, LinearMap.smul_apply, eval, Finsupp.lapply_apply, smul_eq_mul]
    by_cases h : a = m
    · subst a
      simp [basisState]
    · simp [basisState, h]
  have hx := congrArg (fun L => L x) hmap
  simpa only [eval, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
    smul_eq_mul] using hx

/-- Left composition by a diagonal evolution rescales a matrix coefficient by the output
configuration's exponential weight. -/
theorem matrixCoeff_diagonalEvolution_comp
    (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (m n : Config) :
    matrixCoeff ((diagonalEvolution energy τ).comp A) m n =
      Complex.exp ((τ * energy m : ℝ) : ℂ) * matrixCoeff A m n := by
  rw [matrixCoeff, LinearMap.comp_apply, diagonalEvolution_apply_coord]
  rfl

end
end Common
end SecondQuantization
