import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.InteractionPicture

set_option linter.style.header false

/-!
# The bosonic interaction picture

Bosonic specialization of the statistics-independent algebraic interaction-picture API, using the
free bosonic occupation energy.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.interactionPicture (freeEigenvalue ε) V τ

/-- At zero imaginary time, the interaction picture is the original operator. -/
@[simp]
theorem interactionPicture_zero (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    interactionPicture ε V 0 = V :=
  Common.interactionPicture_zero (freeEigenvalue ε) V

/-- Matrix coefficients acquire the free bosonic energy-difference exponential. -/
theorem matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) (m n : Occupation Mode) :
    Common.matrixCoeff (interactionPicture ε V τ) m n =
      Complex.exp ((τ * (freeEigenvalue ε m - freeEigenvalue ε n) : ℝ) : ℂ) *
        Common.matrixCoeff V m n :=
  Common.matrixCoeff_interactionPicture (freeEigenvalue ε) V τ m n

/-- Every bosonic interaction-picture matrix coefficient is continuous in imaginary time. -/
theorem continuous_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (m n : Occupation Mode) :
    Continuous (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n) :=
  Common.continuous_matrixCoeff_interactionPicture (freeEigenvalue ε) V m n

/-- Every bosonic interaction-picture matrix coefficient is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (m n : Occupation Mode) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n)
      MeasureTheory.volume a b :=
  Common.intervalIntegrable_matrixCoeff_interactionPicture (freeEigenvalue ε) V m n a b

end Bosonic
end SecondQuantization
