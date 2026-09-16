import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false

/-!
# Energy-shift eigenoperators of diagonal evolution

A real-valued instance of `CarriesShift` records a fixed energy shift: every nonzero matrix
coefficient connects basis states whose energies differ by the same amount. This support-level
condition is independent of particle statistics and implies the usual imaginary-time eigenoperator
law `A(τ) = exp(τ q) A` under diagonal Heisenberg evolution. The phase is exposed in its canonical
complex form so statistics-specific consumers do not repeat real-to-complex cast normalization.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

/-- A fixed real support shift makes an operator an eigenoperator of diagonal Heisenberg evolution. -/
theorem heisenbergEvolve_eq_smul_of_carriesShift
    (energy : Config → ℝ) (q τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hA : CarriesShift energy A q) :
    heisenbergEvolve energy τ A = Complex.exp ((τ : ℂ) * (q : ℂ)) • A := by
  apply matrixCoeff_ext
  intro m n
  rw [matrixCoeff_heisenbergEvolve]
  change Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff A m n =
    matrixCoeffLinear m n (Complex.exp ((τ : ℂ) * (q : ℂ)) • A)
  rw [map_smul, matrixCoeffLinear_apply]
  by_cases hmn : matrixCoeff A m n = 0
  · simp [hmn]
  · have hshift := hA m n hmn
    have hdiff : energy m - energy n = q := by linarith
    rw [hdiff]
    push_cast
    simp [smul_eq_mul]

/-- Real support-shift eigenoperators satisfy the corresponding KMS-type commutation relation with
the diagonal evolution. -/
theorem diagonalEvolution_comp_of_carriesShift
    (energy : Config → ℝ) (q τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hA : CarriesShift energy A q) :
    (diagonalEvolution energy τ).comp A =
      Complex.exp ((τ : ℂ) * (q : ℂ)) • (A.comp (diagonalEvolution energy τ)) := by
  have hevol :
      heisenbergEvolve energy τ A = Complex.exp ((q * τ : ℝ) : ℂ) • A := by
    have h := heisenbergEvolve_eq_smul_of_carriesShift energy q τ A hA
    simpa [mul_comm] using h
  have hcomp := diagonalEvolution_comp_eq_smul_comp_diagonalEvolution energy τ q A hevol
  simpa [mul_comm] using hcomp

end
end Common
end SecondQuantization
