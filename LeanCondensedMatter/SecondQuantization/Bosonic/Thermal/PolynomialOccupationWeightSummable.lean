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
    rw [hgdef]
    have hr : ‖Real.exp (-β * ε i)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
      linarith [hpos i]
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (power i) hr
    have heq :
        (fun k : ℕ => (k : ℝ) ^ power i * oneModeBoltzmannWeight β (ε i) k) =
          fun k : ℕ => (k : ℝ) ^ power i * Real.exp (-β * ε i) ^ k := by
      funext k
      unfold oneModeBoltzmannWeight
      rw [Real.exp_nat_mul]
    rwa [heq]
  have hnonneg : ∀ i k, 0 ≤ g i k := by
    intro i k
    rw [hgdef]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
  have H := Finsupp.hasSum_prod_nonneg g (fun i => ∑' k, g i k)
    (fun i => (hg i).hasSum) hnonneg
  have heq : (fun n : Occupation Mode => ∏ i, g i (n i)) =
      fun n : Occupation Mode =>
        (∏ i, (n i : ℝ) ^ power i) * boltzmannWeight ε β n := by
    funext n
    rw [boltzmannWeight_eq_prod]
    simp only [hgdef]
    exact Finset.prod_mul_distrib
  rw [heq] at H
  exact H.summable

end
end Bosonic
end SecondQuantization
