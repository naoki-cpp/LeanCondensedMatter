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
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve_apply, imaginaryTimeEvolveFree_basisState, map_smul,
    interactionHamiltonian_basisState, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
    smul_smul]
  congr 1
  have hx : (↑(-τ) : ℂ) * ∑ i ∈ n, (ε i : ℂ) = -((τ : ℂ) * ∑ i ∈ n, (ε i : ℂ)) := by
    push_cast
    ring
  rw [hx, mul_right_comm, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

end Fermionic
end SecondQuantization
