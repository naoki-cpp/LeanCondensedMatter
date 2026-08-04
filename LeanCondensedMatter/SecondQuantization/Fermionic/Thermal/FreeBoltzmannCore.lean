import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Free-fermion Boltzmann weights and partition function

This module owns the finite free-fermion thermal weight and partition function used by canonical
density-state constructions.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The free Boltzmann weight `e^{-βE(n)}` for `E(n) = Σᵢ∈n ε(i)`. -/
noncomputable def freeBoltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℂ :=
  Complex.exp (-(β : ℂ) * ∑ i ∈ n, (ε i : ℂ))

omit [LinearOrder Mode] [Fintype Mode] in
/-- The free Boltzmann weight is a cast of a positive real number. -/
theorem freeBoltzmannWeight_eq_ofReal (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = ((Real.exp (-β * ∑ i ∈ n, ε i) : ℝ) : ℂ) := by
  rw [freeBoltzmannWeight,
    show -(β : ℂ) * ∑ i ∈ n, (ε i : ℂ) = ((-β * ∑ i ∈ n, ε i : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_exp]

omit [LinearOrder Mode] [Fintype Mode] in
theorem freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n ≠ 0 :=
  Complex.exp_ne_zero _

/-- The free partition function `Z₀(β)` as its finite occupation-basis sum. -/
noncomputable def freePartitionFunction (ε : Mode → ℝ) (β : ℝ) : ℂ :=
  ∑ n : Occupation Mode, freeBoltzmannWeight ε β n

omit [LinearOrder Mode] in
/-- The free finite fermion partition function is nonzero. -/
theorem freePartitionFunction_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β ≠ 0 := by
  rw [freePartitionFunction]
  simp_rw [freeBoltzmannWeight_eq_ofReal]
  rw [← Complex.ofReal_sum]
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  exact Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

end Fermionic
end SecondQuantization
