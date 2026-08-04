import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreePartitionFunction

set_option linter.style.header false

/-!
# Free bosonic Boltzmann weight and factorization

This module defines the free Gibbs weight `e^{-βE(n)}` and proves that, for a finite mode type, it
factors into a product of one-mode weights. The factorization is the algebraic input for the
summability and partition-function product formulas.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*}

/-- The free bosonic Boltzmann weight `e^{-βE(n)}`. -/
noncomputable def boltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℝ :=
  Real.exp (-β * freeEigenvalue ε n)

variable [Fintype Mode]

omit in
/-- The free energy is the sum over all modes; terms outside the support vanish. -/
theorem freeEigenvalue_eq_sum_univ (ε : Mode → ℝ) (n : Occupation Mode) :
    freeEigenvalue ε n = ∑ i, (n i : ℝ) * ε i := by
  simp only [freeEigenvalue, Finsupp.sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finsupp.mem_support_iff, not_not] at hi
  rw [hi]
  simp

omit in
/-- The free Boltzmann weight factors into one-mode Boltzmann weights. -/
theorem boltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    boltzmannWeight ε β n = ∏ i, oneModeBoltzmannWeight β (ε i) (n i) := by
  unfold boltzmannWeight oneModeBoltzmannWeight
  rw [freeEigenvalue_eq_sum_univ, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Bosonic
end SecondQuantization
