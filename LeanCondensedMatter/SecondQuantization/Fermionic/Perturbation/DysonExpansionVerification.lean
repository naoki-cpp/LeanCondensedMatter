import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansionVerification
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Fermionic time-independent Dyson verification

The generic time-independent coefficient formula is used directly from `SecondQuantization.Common`.
Only the density-density `interactionHamiltonian` statements remain fermion-specific.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- `interactionHamiltonian` is time-independent in the interaction picture. -/
theorem imaginaryTimeEvolve_interactionHamiltonian (ε : Mode → ℝ) (Vint : Mode → Mode → ℝ)
    (τ : ℝ) : imaginaryTimeEvolve ε τ (interactionHamiltonian Vint) = interactionHamiltonian Vint
    := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve_apply, imaginaryTimeEvolveFree_basisState, map_smul,
    interactionHamiltonian_basisState, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
    smul_smul]
  congr 1
  have hx : (↑(-τ) : ℂ) * ∑ i ∈ n, (ε i : ℂ) = -((τ : ℂ) * ∑ i ∈ n, (ε i : ℂ)) := by
    push_cast; ring
  rw [hx, mul_right_comm, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

omit [LinearOrder Mode] in
/-- The density-density interaction Hamiltonian has the ordinary Taylor Dyson coefficients. -/
theorem dysonCoeff_interactionHamiltonian_eq (ε : Mode → ℝ) (Vint : Mode → Mode → ℝ) (n : ℕ)
    (τ : ℝ) :
    Common.dysonCoeff (fermionEnergy ε) (interactionHamiltonian Vint) n τ =
      ((-τ : ℂ) ^ n / n.factorial) • (interactionHamiltonian Vint) ^ n :=
  Common.dysonCoeff_eq_of_time_independent
    (fermionEnergy ε) (interactionHamiltonian Vint)
    (imaginaryTimeEvolve_interactionHamiltonian ε Vint) n τ

end Fermionic
end SecondQuantization
