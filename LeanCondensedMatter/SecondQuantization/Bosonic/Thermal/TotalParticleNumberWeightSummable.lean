import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.QuadraticParticleNumberWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability of the squared total particle number

The quartic bosonic ladder amplitude can be controlled uniformly by a quadratic polynomial in the
total particle number.  This file converts the modewise quadratic Gibbs estimates into the global
estimate for `particleNumber n ^ 2` by expanding the square as a finite double sum over modes.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- On a finite mode type, the total particle number is the sum of the mode occupations. -/
theorem particleNumber_eq_sum_univ (n : Occupation Mode) :
    particleNumber n = ∑ i, n i := by
  simp only [particleNumber, Finsupp.sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finsupp.mem_support_iff, not_not] at hi
  simp [hi]

/-- The square of the total particle number remains summable against the free bosonic Boltzmann
weight.  This is the uniform degree-two majorant used for quartic ladder amplitudes. -/
theorem summable_particleNumber_total_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      (particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  have hinner : ∀ i : Mode, Summable (fun n : Occupation Mode =>
      ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    intro i
    exact summable_sum fun j (_ : j ∈ Finset.univ) =>
      summable_particleNumber_mul_particleNumber_boltzmannWeight ε β hpos i j
  have hdouble : Summable (fun n : Occupation Mode =>
      ∑ i, ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    exact summable_sum fun i (_ : i ∈ Finset.univ) => hinner i
  refine hdouble.congr fun n => ?_
  rw [particleNumber_eq_sum_univ]
  push_cast
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_mul]

end
end Bosonic
end SecondQuantization
