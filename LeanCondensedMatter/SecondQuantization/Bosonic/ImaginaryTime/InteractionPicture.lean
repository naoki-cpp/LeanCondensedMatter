import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.InteractionPicture

set_option linter.style.header false

/-!
# The bosonic interaction picture

Bosonic specialization of the statistics-independent algebraic interaction-picture operator, using
the free bosonic occupation energy. The operator and its zero-time law require no finite basis.

The fermionic matrix-coefficient continuity API currently uses `[Fintype Config]`; it is
deliberately not copied here because `Occupation Mode := Mode →₀ ℕ` is infinite even when `Mode`
is finite.
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

end Bosonic
end SecondQuantization
