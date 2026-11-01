import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Fermionic scalar KMS denominator

The fermionic statistics sign gives a nonvanishing scalar KMS denominator for every real
energy shift. Generic finite Boltzmann weights are owned by `Common.boltzmannWeight`;
the full-occupation grand-canonical partition function, with explicit `μ`, is owned by
`Common.grandCanonicalPartitionFunction`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

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
