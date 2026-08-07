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

omit [Fintype Mode] in
/-- A finite sum of summable occupation-indexed functions is summable. -/
private theorem summable_finset_sum
    (s : Finset Mode) (f : Mode → Occupation Mode → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : Occupation Mode => (0 : ℝ)))
  | @insert a s ha ih =>
      have hfa : Summable (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, Summable (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hih := ih hfs
      simpa [Finset.sum_insert ha] using hfa.add hih

/-- The square of the total particle number remains summable against the free bosonic Boltzmann
weight.  This is the uniform degree-two majorant used for quartic ladder amplitudes. -/
theorem summable_particleNumber_total_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      (particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  have hinner : ∀ i : Mode, Summable (fun n : Occupation Mode =>
      ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    intro i
    simpa only [Finset.mem_univ, true_implies] using
      summable_finset_sum (Finset.univ : Finset Mode)
        (fun j n => (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n)
        (fun j _ => summable_particleNumber_mul_particleNumber_boltzmannWeight ε β hpos i j)
  have hdouble : Summable (fun n : Occupation Mode =>
      ∑ i, ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    simpa only [Finset.mem_univ, true_implies] using
      summable_finset_sum (Finset.univ : Finset Mode)
        (fun i n => ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n)
        (fun i _ => hinner i)
  convert hdouble using 1
  funext n
  rw [particleNumber_eq_sum_univ]
  push_cast
  calc
    (∑ i, (n i : ℝ)) ^ 2 * boltzmannWeight ε β n =
        ((∑ i, (n i : ℝ)) * (∑ j, (n j : ℝ))) * boltzmannWeight ε β n := by rw [pow_two]
    _ = (∑ i, ∑ j, (n i : ℝ) * (n j : ℝ)) * boltzmannWeight ε β n := by
      rw [Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

end
end Bosonic
end SecondQuantization
