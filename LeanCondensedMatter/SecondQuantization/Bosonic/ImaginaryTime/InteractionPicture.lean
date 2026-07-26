import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The bosonic interaction picture

The interaction-picture operator is the free imaginary-time evolution of an arbitrary algebraic
bosonic operator. Matrix coefficients have the same exponential energy-difference form as in the
fermionic line; no thermal sum, Hilbert-space completion, or operator exponential is used.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  imaginaryTimeEvolve ε τ V

/-- At zero imaginary time, the interaction picture is the original operator. -/
@[simp]
theorem interactionPicture_zero (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    interactionPicture ε V 0 = V :=
  imaginaryTimeEvolve_zero ε V

/-- Matrix coefficients of an interaction-picture operator acquire the free energy-difference
exponential. -/
theorem matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ)
    (m n : Occupation Mode) :
    Common.matrixCoeff (interactionPicture ε V τ) m n =
      Complex.exp ((τ * (freeEigenvalue ε m - freeEigenvalue ε n) : ℝ) : ℂ) *
        Common.matrixCoeff V m n :=
  Common.matrixCoeff_heisenbergEvolve (freeEigenvalue ε) τ V m n

/-- Every matrix coefficient of an interaction-picture operator is continuous in imaginary time. -/
theorem continuous_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (m n : Occupation Mode) :
    Continuous (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n) := by
  simp only [matrixCoeff_interactionPicture]
  fun_prop

/-- Every matrix coefficient of an interaction-picture operator is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (m n : Occupation Mode) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_interactionPicture ε V m n).intervalIntegrable a b

end Bosonic
end SecondQuantization
