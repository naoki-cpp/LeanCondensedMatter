import LeanCondensedMatter.Analysis.FinsuppProductSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.BoltzmannWeightFactorization

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# The multi-mode free Boltzmann weight is summable, with total weight `∏ᵢ (1 - e^{-βεᵢ})⁻¹`

Phase B3c of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the genuine
(uncutoff) infinite sum `Σ_n e^{-βE(n)}` over *all* of `Occupation Mode`, for a finite mode set,
converges to the product of one-mode geometric series from `FreePartitionFunction.lean` whenever
every mode satisfies the one-mode convergence condition `0 < βεᵢ`. This is the multi-mode
generalization `BoltzmannWeightFactorization.lean` flagged as remaining.

The proof is a thin corollary of the general (non-physics) `Finsupp.hasSum_prod_nonneg` fact
proved in `Analysis/FinsuppProductSeries.lean`: `boltzmannWeight_eq_prod` identifies the Boltzmann
weight with the multi-index product `∏ i, oneModeBoltzmannWeight β (ε i) (n i)`, and each
one-mode factor is nonnegative and `HasSum`-convergent by `hasSum_oneModeBoltzmannWeight`, so the
nonnegative (rather than absolute-value) version of the general theorem applies directly.
-/

namespace SecondQuantization
namespace Bosonic

/-- **The genuine multi-mode free Boltzmann weight is summable**, converging to the
product of one-mode geometric series, given every mode's one-mode convergence condition
`0 < βεᵢ`. -/
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

/-- **The genuine multi-mode free partition function is strictly positive**: each one-mode factor
`(1 - e^{-βεᵢ})⁻¹` is positive under the convergence condition `0 < βεᵢ`, hence so is their finite
product. -/
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
