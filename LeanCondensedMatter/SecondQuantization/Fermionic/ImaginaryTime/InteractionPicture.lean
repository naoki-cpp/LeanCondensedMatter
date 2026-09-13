import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The fermionic interaction picture

The physical interaction-picture operator is the fermionic specialization of the
statistics-independent `Common.interactionPicture`. Generic algebraic and analytic facts are
consumed from `SecondQuantization.Common` directly rather than re-exported under duplicate
fermionic theorem names. The density-density interaction's time independence is kept here beside
the evolution that proves it.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode]

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (τ : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.interactionPicture (fermionEnergy ε) V τ

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- `interactionHamiltonian` is time-independent under free imaginary-time evolution. -/
theorem imaginaryTimeEvolve_interactionHamiltonian (ε : Mode → ℝ) (Vint : Mode → Mode → ℝ)
    (τ : ℝ) : imaginaryTimeEvolve ε τ (interactionHamiltonian Vint) = interactionHamiltonian Vint := by
  simpa only [imaginaryTimeEvolve, interactionHamiltonian] using
    Common.heisenbergEvolve_diagonalOperator (fermionEnergy ε) τ
      (fun n : Occupation Mode => (∑ i ∈ n, ∑ j ∈ n, (Vint i j : ℂ)))

end Fermionic
end SecondQuantization
