import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightSummable

set_option linter.style.header false

/-!
# Polynomial occupation moments of the free bosonic Gibbs weight

Fixed finite products of bosonic ladder operators have occupation-basis coefficients with polynomial
growth.  This module owns the reusable finite-mode polynomial majorants for the genuinely infinite
bosonic occupation space.  The quadratic total-particle-number estimate at the end of this module specializes these
polynomial majorants; it adds no analytic input to their proof.

On a finite mode type, each mode contributes a one-dimensional series `k^p r^k`, which is summable
for `|r| < 1`; `Finsupp.hasSum_prod_nonneg` then reconstructs the infinite occupation-space sum.
Mode-dependent shifted powers use one analytic interface for monomials and tails of finite ladder
products.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

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

variable {Mode : Type*} [Fintype Mode]

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

/-!
## Quadratic total-particle-number moment

The following bound is a direct finite-mode specialization of the general polynomial majorant.
-/

set_option linter.unusedFintypeInType false

/-! ## Total particle number -/

/-- The square of the total particle number remains summable against the free bosonic
Boltzmann weight, providing a degree-two moment bound for quartic ladder amplitudes. -/
theorem summable_particleNumber_total_sq_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      (particleNumber n : ℝ) ^ 2 * boltzmannWeight ε β n) := by
  have hpair (i j : Mode) :
      Summable (fun n : Occupation Mode =>
        (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    classical
    have h := summable_shiftedOccupationPowerProduct_boltzmannWeight ε β hpos (fun _ => 0)
      (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
    refine h.congr fun n => ?_
    simp only [Nat.add_zero, pow_add, Finset.prod_mul_distrib]
    congr 1
    have hprod (k : Mode) :
        (∏ l : Mode, (n l : ℝ) ^ (if l = k then 1 else 0 : ℕ)) = (n k : ℝ) := by
      rw [Fintype.prod_eq_single k]
      · simp
      · intro l hl
        simp [hl]
    rw [hprod i, hprod j]
  have hinner : ∀ i : Mode, Summable (fun n : Occupation Mode =>
      ∑ j, (n i : ℝ) * (n j : ℝ) * boltzmannWeight ε β n) := by
    intro i
    exact summable_sum fun j (_ : j ∈ Finset.univ) =>
      hpair i j
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
