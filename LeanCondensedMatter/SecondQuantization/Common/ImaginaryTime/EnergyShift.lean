import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Energy-shift eigenoperators of diagonal evolution

An operator has energy shift `q` when every nonzero matrix coefficient connects basis states whose
free energies differ by exactly `q`. This support-level condition is independent of particle
statistics and implies the usual imaginary-time eigenoperator law
`A(τ) = exp(τ q) A` under diagonal Heisenberg evolution.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- `A` has a fixed energy shift `q` relative to the diagonal basis energy `energy` when every
nonzero matrix element `Aₘₙ` satisfies `energy m - energy n = q`. -/
def HasEnergyShift (energy : Config → ℝ) (q : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : Prop :=
  ∀ m n, matrixCoeff A m n ≠ 0 → energy m - energy n = q

/-- A fixed support-level energy shift makes an operator an eigenoperator of diagonal Heisenberg
evolution. -/
theorem heisenbergEvolve_eq_smul_of_hasEnergyShift
    (energy : Config → ℝ) (q τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hA : HasEnergyShift energy q A) :
    heisenbergEvolve energy τ A = Complex.exp ((τ * q : ℝ) : ℂ) • A := by
  apply matrixCoeff_ext
  intro m n
  rw [matrixCoeff_heisenbergEvolve]
  change Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff A m n =
    matrixCoeffLinear m n (Complex.exp ((τ * q : ℝ) : ℂ) • A)
  rw [map_smul, matrixCoeffLinear_apply]
  by_cases hmn : matrixCoeff A m n = 0
  · simp [hmn]
  · rw [hA m n hmn]
    simp [smul_eq_mul]

/-- Energy-shift eigenoperators satisfy the corresponding KMS-type commutation relation with the
diagonal evolution. -/
theorem diagonalEvolution_comp_of_hasEnergyShift
    (energy : Config → ℝ) (q τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hA : HasEnergyShift energy q A) :
    (diagonalEvolution energy τ).comp A =
      Complex.exp ((q * τ : ℝ) : ℂ) • (A.comp (diagonalEvolution energy τ)) := by
  apply diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
  have h := heisenbergEvolve_eq_smul_of_hasEnergyShift energy q τ A hA
  simpa [mul_comm] using h

end
end Common
end SecondQuantization
