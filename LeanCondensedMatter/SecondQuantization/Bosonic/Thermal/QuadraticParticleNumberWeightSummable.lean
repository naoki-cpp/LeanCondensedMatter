import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ParticleNumberWeightSummable

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability of quadratic particle-number-weighted bosonic Gibbs weights

Quartic bosonic matrix coefficients grow at most quadratically in occupation numbers.  This file
provides the corresponding free-Boltzmann summability estimate on the genuinely infinite bosonic
occupation space.  No closed form is needed: Mathlib's polynomially weighted geometric-series
summability supplies the one-mode input, and the existing finite-product Finsupp theorem lifts it
to finitely many modes.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality used by finite-mode product decompositions. -/
local instance instDecidableEqQuadraticParticleNumberWeightSummable : DecidableEq Mode :=
  Classical.decEq Mode

/-- A square occupation-number weight remains summable against the free bosonic Boltzmann weight. -/
theorem summable_particleNumber_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    Summable (fun n : Occupation Mode => (n j : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  set g : Mode → ℕ → ℝ := fun i k =>
    if i = j then (k : ℝ) ^ 2 * oneModeBoltzmannWeight β (ε i) k
    else oneModeBoltzmannWeight β (ε i) k with hgdef
  have hg : ∀ i, Summable (g i) := by
    intro i
    rw [hgdef]
    dsimp only
    split_ifs with hi
    · subst j
      have hr : ‖Real.exp (-β * ε i)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
        linarith [hpos i]
      have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
      exact h.congr fun k => by
        unfold oneModeBoltzmannWeight
        rw [Real.exp_nat_mul]
    · exact (hasSum_oneModeBoltzmannWeight (hpos i)).summable
  have hnonneg : ∀ i k, 0 ≤ g i k := by
    intro i k
    rw [hgdef]
    dsimp only
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have H := Finsupp.hasSum_prod_nonneg g (fun i => ∑' k, g i k)
    (fun i => (hg i).hasSum) hnonneg
  exact (HasSum.congr_fun H fun n => by
    symm
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (n i)) (Finset.mem_univ j), hgdef]
    simp only [if_true]
    have hrest : ∀ i, i ∈ Finset.univ.erase j →
        g i (n i) = oneModeBoltzmannWeight β (ε i) (n i) := fun i hi => by
      rw [hgdef]
      simp [Finset.ne_of_mem_erase hi]
    rw [Finset.prod_congr rfl hrest, mul_assoc, boltzmannWeight_eq_prod,
      Finset.mul_prod_erase Finset.univ (fun i => oneModeBoltzmannWeight β (ε i) (n i))
        (Finset.mem_univ j)]).summable

/-- A product of two occupation numbers remains summable against the free bosonic Boltzmann weight.
This is the degree-two estimate needed for diagonal matrix coefficients of quartic interactions. -/
theorem summable_particleNumber_mul_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (i j : Mode) :
    Summable (fun n : Occupation Mode =>
      (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
  have hi := summable_particleNumber_sq_boltzmannWeight ε β hpos i
  have hj := summable_particleNumber_sq_boltzmannWeight ε β hpos j
  have hmajorant : Summable (fun n : Occupation Mode =>
      (1 / 2 : ℝ) *
        ((n i : ℝ) ^ 2 * boltzmannWeight ε β n +
          (n j : ℝ) ^ 2 * boltzmannWeight ε β n)) := by
    exact (hi.add hj).mul_left (1 / 2 : ℝ)
  apply hmajorant.of_norm_bounded
  intro n
  have hni : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  have hnj : 0 ≤ (n j : ℝ) := Nat.cast_nonneg _
  have hw : 0 ≤ boltzmannWeight ε β n := by
    exact Real.exp_nonneg _
  have hab : (n i : ℝ) * (n j : ℝ) ≤ ((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2) / 2 := by
    nlinarith [sq_nonneg ((n i : ℝ) - (n j : ℝ))]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hni hnj) hw)]
  calc
    (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n ≤
        (((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2) / 2) * boltzmannWeight ε β n :=
      mul_le_mul_of_nonneg_right hab hw
    _ = (1 / 2 : ℝ) *
        ((n i : ℝ) ^ 2 * boltzmannWeight ε β n +
          (n j : ℝ) ^ 2 * boltzmannWeight ε β n) := by ring

end
end Bosonic
end SecondQuantization
