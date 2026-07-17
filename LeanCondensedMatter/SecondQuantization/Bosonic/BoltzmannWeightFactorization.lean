import LeanCondensedMatter.SecondQuantization.Bosonic.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The multi-mode free Boltzmann weight factors into one-mode factors

Phase B3b of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): for a *finite* mode
set, the free Boltzmann weight `e^{-βE(n)}` factors as a finite product of the one-mode weights
from `FreePartitionFunction.lean`, `E(n) = Σᵢ n(i)·ε(i)` being additive over modes.

This is the purely algebraic half of the multi-mode partition-function product formula
`Z(β) = ∏ᵢ (1-e^{-βεᵢ})⁻¹`. **What remains** (B3c, not yet started): the actual infinite-sum
decomposition `Σ_n ∏ᵢ q_i^{n(i)} = ∏ᵢ Σ_k q_i^k`, by induction on `[Fintype Mode]`
(`Fintype.induction_empty_option`) combined with Mathlib's
`Finsupp.optionEquiv : (Option α →₀ M) ≃ M × (α →₀ M)` (giving
`Occupation (Option Mode) ≃ ℕ × Occupation Mode` at each inductive step) and
`tsum_mul_tsum_of_summable_norm`/`HasSum.mul` to combine the two factors' `HasSum` facts. This
factorization lemma is exactly the per-`n` identity that decomposition needs as its base
ingredient.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- **The multi-mode free Boltzmann weight**, `e^{-βE(n)}`, for a finite mode set. -/
noncomputable def boltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℝ :=
  Real.exp (-β * freeEigenvalue ε n)

omit [DecidableEq Mode] in
/-- **`freeEigenvalue` as a sum over all of `Mode`**, not just `n`'s support — valid since a
finitely-supported summand contributes `0` outside its support, and `Mode` is finite here. -/
theorem freeEigenvalue_eq_sum_univ (ε : Mode → ℝ) (n : Occupation Mode) :
    freeEigenvalue ε n = ∑ i, (n i : ℝ) * ε i := by
  simp only [freeEigenvalue, Finsupp.sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Finsupp.mem_support_iff, not_not] at hi
  rw [hi]
  simp

omit [DecidableEq Mode] in
/-- **The multi-mode Boltzmann weight factors into one-mode factors**:
`e^{-βE(n)} = ∏ᵢ e^{-β n(i) ε(i)}`. The algebraic core of the product formula for `Z(β)`. -/
theorem boltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    boltzmannWeight ε β n = ∏ i, oneModeBoltzmannWeight β (ε i) (n i) := by
  unfold boltzmannWeight oneModeBoltzmannWeight
  rw [freeEigenvalue_eq_sum_univ, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Bosonic
end SecondQuantization
