import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# The fermionic interaction picture

Fermionic specialization of the statistics-independent algebraic interaction-picture API, using
the free fermionic occupation energy.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.interactionPicture (fermionEnergy ε) V τ

omit [LinearOrder Mode] [Fintype Mode] in
/-- At zero imaginary time, the interaction picture is the original operator. -/
@[simp]
theorem interactionPicture_zero (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    interactionPicture ε V 0 = V :=
  Common.interactionPicture_zero (fermionEnergy ε) V

omit [LinearOrder Mode] in
/-- Matrix coefficients acquire the free fermionic energy-difference exponential. -/
theorem matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ)
    (m n : FermionOccupation Mode) :
    Common.matrixCoeff (interactionPicture ε V τ) m n =
      Complex.exp ((τ * (fermionEnergy ε m - fermionEnergy ε n) : ℝ) : ℂ) *
        Common.matrixCoeff V m n :=
  Common.matrixCoeff_interactionPicture (fermionEnergy ε) V τ m n

omit [LinearOrder Mode] in
/-- Every fermionic interaction-picture matrix coefficient is continuous in imaginary time. -/
theorem continuous_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) :
    Continuous (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n) :=
  Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε) V m n

omit [LinearOrder Mode] in
/-- Every fermionic interaction-picture matrix coefficient is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n)
      MeasureTheory.volume a b :=
  Common.intervalIntegrable_matrixCoeff_interactionPicture (fermionEnergy ε) V m n a b

end SecondQuantization
