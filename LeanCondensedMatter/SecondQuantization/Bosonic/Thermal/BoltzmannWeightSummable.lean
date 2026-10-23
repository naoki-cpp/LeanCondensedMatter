import LeanCondensedMatter.Analysis.InfiniteSum.FinsuppProduct
import LeanCondensedMatter.Analysis.InfiniteSum.Truncation
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightFactorization

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Summability of the free bosonic Boltzmann weight

For a finite mode type, the sum over all bosonic occupation states converges whenever every mode
satisfies `0 < β ε i`. The total weight is the product of the one-mode geometric-series values.

The proof is a direct specialization of `Finsupp.hasSum_prod_nonneg`, using
`boltzmannWeight_eq_prod` and the one-mode summability theorem.
-/

namespace SecondQuantization
namespace Bosonic

open Filter Topology

/-- The free multi-mode Boltzmann weight has the expected product sum. -/
theorem hasSum_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    HasSum (boltzmannWeight ε β) (∏ i, (1 - Real.exp (-β * ε i))⁻¹) := by
  rw [show boltzmannWeight ε β =
    fun n => ∏ i, oneModeBoltzmannWeight β (ε i) (n i) from funext (boltzmannWeight_eq_prod ε β)]
  exact Finsupp.hasSum_prod_nonneg (fun i k => oneModeBoltzmannWeight β (ε i) k)
    (fun i => (1 - Real.exp (-β * ε i))⁻¹)
    (fun i => hasSum_oneModeBoltzmannWeight (hpos i))
    (fun i k => Real.exp_nonneg _)

theorem summable_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) : Summable (boltzmannWeight ε β) :=
  (hasSum_boltzmannWeight ε β hpos).summable

theorem tsum_boltzmannWeight {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ)
    (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    ∑' n, boltzmannWeight ε β n = ∏ i, (1 - Real.exp (-β * ε i))⁻¹ :=
  (hasSum_boltzmannWeight ε β hpos).tsum_eq

/-- The free bosonic partition sum is strictly positive. -/
theorem tsum_boltzmannWeight_pos {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) : 0 < ∑' n, boltzmannWeight ε β n := by
  rw [tsum_boltzmannWeight ε β hpos]
  refine Finset.prod_pos fun i _ => inv_pos.2 ?_
  have hnorm : Real.exp (-β * ε i) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith [hpos i]
  linarith

theorem tsum_boltzmannWeight_ne_zero {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) : (∑' n, boltzmannWeight ε β n) ≠ 0 :=
  ne_of_gt (tsum_boltzmannWeight_pos ε β hpos)

/-! ## Particle-number cutoff convergence -/

/-- The free bosonic partition weight has convergent partial sums under particle-number
cutoffs, by the same mask convergence theorem as fermionic mode truncation. -/
theorem tendsto_tsum_boltzmannWeight_particleNumberTruncation
    {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    Tendsto (fun N : ℕ => ∑' n : Occupation Mode,
      if particleNumber n ≤ N then boltzmannWeight ε β n else 0)
      atTop (𝓝 (∑' n, boltzmannWeight ε β n)) := by
  exact tendsto_tsum_ite_of_eventually (boltzmannWeight ε β)
    (summable_boltzmannWeight ε β hpos).norm
    (atTop : Filter ℕ)
    (fun N (n : Occupation Mode) => particleNumber n ≤ N)
    (fun n => eventually_ge_atTop (particleNumber n))

/-- Normalized particle-number-cutoff Boltzmann weights converge pointwise to the free
bosonic Gibbs probabilities. Positivity of the full partition sum follows from the usual
strict one-mode energy condition. -/
theorem tendsto_normalized_boltzmannWeight_particleNumberTruncation
    {Mode : Type*} [Fintype Mode] (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (n : Occupation Mode) :
    Tendsto (fun N : ℕ => Real.normalizedWeight
      (fun m : Occupation Mode =>
        if particleNumber m ≤ N then boltzmannWeight ε β m else 0) n)
      atTop (𝓝 (Real.normalizedWeight (boltzmannWeight ε β) n)) := by
  exact tendsto_normalizedWeight_ite_of_eventually
    (boltzmannWeight ε β) (summable_boltzmannWeight ε β hpos).norm
    (tsum_boltzmannWeight_ne_zero ε β hpos)
    (atTop : Filter ℕ)
    (fun N (m : Occupation Mode) => particleNumber m ≤ N)
    (fun m => eventually_ge_atTop (particleNumber m)) n

end Bosonic
end SecondQuantization
