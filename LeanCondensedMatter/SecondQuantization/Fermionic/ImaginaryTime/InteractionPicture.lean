import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The fermionic interaction picture

The physical interaction-picture operator is retained as the fermionic specialization of the
statistics-independent `Common.interactionPicture`. Generic algebraic and analytic facts are
consumed from `SecondQuantization.Common` directly rather than re-exported under duplicate
fermionic theorem names.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.interactionPicture (fermionEnergy ε) V τ

end Fermionic
end SecondQuantization
