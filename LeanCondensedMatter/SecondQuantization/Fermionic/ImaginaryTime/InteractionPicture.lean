import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The fermionic interaction picture

The physical interaction-picture operator is retained as the fermionic specialization of the
statistics-independent `Common.interactionPicture`. Generic zero-time, matrix-coefficient, and
integrability facts are consumed from `SecondQuantization.Common` directly rather than re-exported
under duplicate fermionic theorem names.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.interactionPicture (fermionEnergy ε) V τ

/-- Every fermionic interaction-picture matrix coefficient is continuous in imaginary time.

This specialization remains temporarily because it is used by the fermionic quartic-diagram
continuity proofs; the underlying result is `Common.continuous_matrixCoeff_interactionPicture`.
-/
theorem continuous_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (m n : Occupation Mode) :
    Continuous (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n) :=
  Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε) V m n

end Fermionic
end SecondQuantization
