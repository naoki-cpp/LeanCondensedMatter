import LeanCondensedMatter.Analysis.InfiniteSum.FinsuppProduct
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free bosonic Boltzmann weights, factorization, and summability

Define the free Gibbs weight `e^{-βE(n)}` and factor it into one-mode weights.
For finite mode types, the sum over occupation states converges if every mode satisfies
`0 < β ε i`, and the total weight equals the product of the one-mode geometric series.

The one-mode series is geometric and is summable exactly when `0 < β ε`.
The multi-mode summability proof specializes `Finsupp.hasSum_prod_nonneg` using the algebraic factorization
and the one-mode summability theorem.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

/-- The one-mode bosonic Boltzmann weight `e^{-βkε}`. -/
noncomputable def oneModeBoltzmannWeight (β ε : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) * (-β * ε))

/-- The one-mode Boltzmann series sums to the geometric-series value when `0 < βε`. -/
theorem hasSum_oneModeBoltzmannWeight {β ε : ℝ} (h : 0 < β * ε) :
    HasSum (oneModeBoltzmannWeight β ε) (1 - Real.exp (-β * ε))⁻¹ := by
  have hnorm : ‖Real.exp (-β * ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hgeo := hasSum_geometric_of_norm_lt_one hnorm
  unfold oneModeBoltzmannWeight
  simpa only [Real.exp_nat_mul] using hgeo

/-- The one-mode Boltzmann series is summable exactly when `0 < βε`. -/
theorem summable_oneModeBoltzmannWeight_iff {β ε : ℝ} :
    Summable (oneModeBoltzmannWeight β ε) ↔ 0 < β * ε := by
  unfold oneModeBoltzmannWeight
  simp_rw [Real.exp_nat_mul]
  rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqBoltzmannWeightFactorization : DecidableEq Mode := Classical.decEq Mode

/-- The free bosonic Boltzmann weight `e^{-βE(n)}`. -/
noncomputable def boltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℝ :=
  Real.exp (-β * freeEigenvalue ε n)

variable [Fintype Mode]

/-- The free Boltzmann weight factors into one-mode Boltzmann weights. -/
theorem boltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    boltzmannWeight ε β n = ∏ i, oneModeBoltzmannWeight β (ε i) (n i) := by
  unfold boltzmannWeight oneModeBoltzmannWeight
  have henergy : freeEigenvalue ε n = ∑ i, (n i : ℝ) * ε i := by
    rw [freeEigenvalue_eq_finsupp_sum]
    simp only [Finsupp.sum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [Finsupp.mem_support_iff, not_not] at hi
    rw [hi]
    simp
  rw [henergy, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end

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

end Bosonic
end SecondQuantization
