import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Summability of particle-number-weighted bosonic Gibbs weights

For a fixed mode `j`, the series `Σ n, n(j) e^{-βE(n)}` converges under the same positivity
assumption as the partition sum. The proof replaces the `j`th one-mode geometric series by its
index-weighted version and applies the same finite-product `Finsupp` summation theorem.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- The particle-number-weighted free Boltzmann series has its product closed form. -/
theorem hasSum_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    HasSum (fun n : Occupation Mode => (n j : ℝ) * boltzmannWeight ε β n)
      (Real.exp (-β * ε j) / (1 - Real.exp (-β * ε j)) ^ 2 *
        ∏ i ∈ Finset.univ.erase j, (1 - Real.exp (-β * ε i))⁻¹) := by
  set g' : Mode → ℕ → ℝ := fun i k =>
    if i = j then (k : ℝ) * oneModeBoltzmannWeight β (ε i) k
    else oneModeBoltzmannWeight β (ε i) k with hg'def
  set b' : Mode → ℝ := fun i =>
    if i = j then Real.exp (-β * ε j) / (1 - Real.exp (-β * ε j)) ^ 2
    else (1 - Real.exp (-β * ε i))⁻¹ with hb'def
  have hg' : ∀ i, HasSum (g' i) (b' i) := by
    intro i
    rw [hg'def, hb'def]
    by_cases hi : i = j
    · subst hi
      simp only [if_true]
      have hr : ‖Real.exp (-β * ε i)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
        linarith [hpos i]
      have h := hasSum_coe_mul_geometric_of_norm_lt_one hr
      have heq : (fun k : ℕ => (k : ℝ) * oneModeBoltzmannWeight β (ε i) k) =
          fun k : ℕ => (k : ℝ) * Real.exp (-β * ε i) ^ k := by
        funext k
        unfold oneModeBoltzmannWeight
        rw [Real.exp_nat_mul]
      rw [heq]
      exact h
    · simp only [if_neg hi]
      exact hasSum_oneModeBoltzmannWeight (hpos i)
  have hnn' : ∀ i n, 0 ≤ g' i n := by
    intro i n
    rw [hg'def]
    by_cases hi : i = j
    · simp only [if_pos hi]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
    · simp only [if_neg hi]
      exact Real.exp_nonneg _
  have H := Finsupp.hasSum_prod_nonneg g' b' hg' hnn'
  have hprod : ∀ i, i ∈ Finset.univ.erase j →
      b' i = (1 - Real.exp (-β * ε i))⁻¹ := fun i hi => by
    rw [hb'def]; simp [Finset.ne_of_mem_erase hi]
  rw [← Finset.mul_prod_erase Finset.univ b' (Finset.mem_univ j), hb'def] at H
  simp only [if_true] at H
  rw [Finset.prod_congr rfl hprod] at H
  have heq : (fun n : Occupation Mode => ∏ i, g' i (n i)) =
      (fun n : Occupation Mode => (n j : ℝ) * boltzmannWeight ε β n) := by
    funext n
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g' i (n i)) (Finset.mem_univ j), hg'def]
    simp only [if_true]
    have hrest : ∀ i, i ∈ Finset.univ.erase j →
        g' i (n i) = oneModeBoltzmannWeight β (ε i) (n i) := fun i hi => by
      rw [hg'def]; simp [Finset.ne_of_mem_erase hi]
    rw [Finset.prod_congr rfl hrest, mul_assoc, boltzmannWeight_eq_prod,
      Finset.mul_prod_erase Finset.univ (fun i => oneModeBoltzmannWeight β (ε i) (n i))
        (Finset.mem_univ j)]
  rwa [heq] at H

theorem summable_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    Summable (fun n : Occupation Mode => (n j : ℝ) * boltzmannWeight ε β n) :=
  (hasSum_particleNumber_boltzmannWeight ε β hpos j).summable

end Bosonic
end SecondQuantization
