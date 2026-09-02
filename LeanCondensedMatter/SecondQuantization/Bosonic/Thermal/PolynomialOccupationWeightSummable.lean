import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.QuadraticParticleNumberWeightSummable

set_option linter.style.header false

/-!
# Polynomial occupation moments of the free bosonic Gibbs weight

Fixed finite products of bosonic ladder operators have occupation-basis coefficients with polynomial
growth.  For the multi-point Gibbs/KMS recursion we therefore need more than the linear and
quadratic special cases: every finite occupation monomial must remain summable against the free
Boltzmann weight.

On a finite mode type this follows directly from the product structure of the free weight.  Each
mode contributes a one-dimensional series `k^p r^k`, which is summable for `|r| < 1`; the existing
`Finsupp.hasSum_prod_nonneg` theorem then reconstructs the genuinely infinite occupation-space sum.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Every finite-mode occupation monomial is summable against the free bosonic Boltzmann weight.

`power i` is the exponent of the occupation number in mode `i`.  This is the reusable polynomial
majorant needed for arbitrary fixed-length products of creation and annihilation operators. -/
theorem summable_occupationMonomial_boltzmannWeight
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) (power : Mode → ℕ) :
    Summable (fun n : Occupation Mode =>
      (∏ i, (n i : ℝ) ^ power i) * boltzmannWeight ε β n) := by
  set g : Mode → ℕ → ℝ := fun i k =>
    (k : ℝ) ^ power i * oneModeBoltzmannWeight β (ε i) k with hgdef
  have hg : ∀ i, Summable (g i) := by
    intro i
    have hr : ‖Real.exp (-β * ε i)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
      linarith [hpos i]
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (power i) hr
    change Summable (fun k : ℕ =>
      (k : ℝ) ^ power i * oneModeBoltzmannWeight β (ε i) k)
    exact h.congr fun k => by
      unfold oneModeBoltzmannWeight
      rw [Real.exp_nat_mul]
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

/-- A uniform shifted power in every mode is summable against the free bosonic Gibbs weight.

This product-form majorant is convenient for arbitrary fixed-length ladder products: after at most
`shift` ladder steps, every intermediate mode occupation is bounded by `n i + shift`. -/
theorem summable_shiftedOccupationPowerProduct_boltzmannWeight
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) (shift power : ℕ) :
    Summable (fun n : Occupation Mode =>
      (∏ i, ((n i + shift : ℕ) : ℝ) ^ power) * boltzmannWeight ε β n) := by
  set g : Mode → ℕ → ℝ := fun i k =>
    ((k + shift : ℕ) : ℝ) ^ power * oneModeBoltzmannWeight β (ε i) k with hgdef
  have hg : ∀ i, Summable (g i) := by
    intro i
    rw [hgdef]
    exact summable_shiftedPow_oneModeBoltzmannWeight β (ε i) (hpos i) shift power
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
