import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Free-fermion Boltzmann weights and partition function

This module owns the finite complex-coordinate free-fermion Boltzmann weight and partition
function used by perturbative and algebraic finite-sum calculations. The canonical physical Gibbs
state and real partition function are owned by `QuantumTheory.Gibbs.PurePoint`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The free Boltzmann weight `e^{-βE(n)}` specialized from the canonical Common weight at
`fermionEnergy`. -/
noncomputable def freeBoltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℂ :=
  Common.boltzmannWeight (fermionEnergy ε) β n

omit [LinearOrder Mode] [Fintype Mode] in
/-- The free Boltzmann weight is a cast of a positive real number. -/
theorem freeBoltzmannWeight_eq_ofReal (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = ((Real.exp (-β * ∑ i ∈ n, ε i) : ℝ) : ℂ) := by
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy, Complex.ofReal_exp]

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

/-- The Bloch--de Dominicis non-resonance denominator is automatically nonzero for fermionic
statistics and any real energy shift and inverse temperature. -/
theorem one_sub_zetaInt_fermion_mul_exp_ne_zero (x β : ℝ) :
    (1 : ℂ) - ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ) * Complex.exp ((x * β : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + Real.exp (x * β) := by
    positivity
  have heq : (1 : ℂ) - ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ) *
      Complex.exp ((x * β : ℝ) : ℂ) = ((1 + Real.exp (x * β) : ℝ) : ℂ) := by
    rw [Common.Statistics.zetaInt_fermion]
    push_cast [Complex.ofReal_exp]
    ring
  rw [heq]
  exact_mod_cast hpos.ne'

end Fermionic
end SecondQuantization
