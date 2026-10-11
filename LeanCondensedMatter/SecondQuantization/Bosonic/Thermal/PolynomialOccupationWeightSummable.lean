import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightSummable

set_option linter.style.header false

/-!
# Polynomial occupation moments of the free bosonic Gibbs weight

Fixed finite products of bosonic ladder operators have occupation-basis coefficients with polynomial
growth.  This module owns the reusable finite-mode polynomial majorants for the genuinely infinite
bosonic occupation space.  Quadratic and total-particle-number estimates specialize this layer;
they do not supply analytic input back to it.

On a finite mode type, each mode contributes a one-dimensional series `k^p r^k`, which is summable
for `|r| < 1`; `Finsupp.hasSum_prod_nonneg` then reconstructs the infinite occupation-space sum.
Mode-dependent shifted powers use one analytic interface for monomials and tails of finite ladder
products.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

omit [Fintype Mode] in
/-- A fixed shift of the occupation number does not spoil polynomially weighted one-mode Gibbs
summability.  This is the tail form needed after finitely many creation operators have acted. -/
theorem summable_shiftedPow_oneModeBoltzmannWeight
    (β energy : ℝ) (hpos : 0 < β * energy) (shift power : ℕ) :
    Summable (fun k : ℕ =>
      ((k + shift : ℕ) : ℝ) ^ power * oneModeBoltzmannWeight β energy k) := by
  let r : ℝ := Real.exp (-β * energy)
  have hr : ‖r‖ < 1 := by
    change ‖Real.exp (-β * energy)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hr0 : r ≠ 0 := by
    dsimp [r]
    exact Real.exp_ne_zero _
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) power hr
  have htail : Summable (fun k : ℕ =>
      ((k + shift : ℕ) : ℝ) ^ power * r ^ (k + shift)) := by
    change Summable ((fun n : ℕ => (n : ℝ) ^ power * r ^ n) ∘ fun k : ℕ => k + shift)
    exact h.comp_injective (fun _ _ hk => Nat.add_right_cancel hk)
  have hscaled := htail.mul_left (r ^ shift)⁻¹
  exact hscaled.congr fun k => by
    symm
    unfold oneModeBoltzmannWeight
    rw [Real.exp_nat_mul]
    change ((↑(k + shift) : ℝ) ^ power * r ^ k) =
      (r ^ shift)⁻¹ * ((↑(k + shift) : ℝ) ^ power * r ^ (k + shift))
    rw [pow_add]
    field_simp [hr0]

/-- Mode-dependent shifted occupation powers are summable against the free bosonic Gibbs weight.

Each mode has its own natural-number shift and power. Zero shifts give occupation monomials;
constant shifts and powers give the majorants needed by fixed-length ladder products. -/
theorem summable_shiftedOccupationPowerProduct_boltzmannWeight
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) (shift power : Mode → ℕ) :
    Summable (fun n : Occupation Mode =>
      (∏ i, ((n i + shift i : ℕ) : ℝ) ^ power i) * boltzmannWeight ε β n) := by
  set g : Mode → ℕ → ℝ := fun i k =>
    ((k + shift i : ℕ) : ℝ) ^ power i * oneModeBoltzmannWeight β (ε i) k with hgdef
  have hg : ∀ i, Summable (g i) := by
    intro i
    rw [hgdef]
    exact summable_shiftedPow_oneModeBoltzmannWeight β (ε i) (hpos i) (shift i) (power i)
  have hnonneg : ∀ i k, 0 ≤ g i k := by
    intro i k
    rw [hgdef]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
  have H := Finsupp.hasSum_prod_nonneg g (fun i => ∑' k, g i k)
    (fun i => (hg i).hasSum) hnonneg
  exact (HasSum.congr_fun H fun n => by
    symm
    rw [boltzmannWeight_eq_prod]
    simp only [hgdef]
    exact Finset.prod_mul_distrib).summable

end
end Bosonic
end SecondQuantization
