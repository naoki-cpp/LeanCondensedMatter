import LeanCondensedMatter.Analysis.FinsuppProductSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightFactorization

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

end Bosonic
end SecondQuantization
