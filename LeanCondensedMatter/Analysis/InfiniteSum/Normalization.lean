import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option linter.style.header false

/-!
# Normalization of summable real weights

Scalar normalization and its laws do not require a Hilbert basis or an operator.
Unit total mass requires a nonzero sum; nonnegativity and the pointwise upper bound
are stated separately.
-/

noncomputable section

namespace Real

variable {ι : Type*}

/-- Normalize a real family by its total sum. -/
def normalizedWeight (a : ι → ℝ) (i : ι) : ℝ :=
  (∑' j, a j)⁻¹ * a i

/-- Absolute summability is preserved by normalization. -/
theorem summable_norm_normalizedWeight (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) :
    Summable fun i => ‖normalizedWeight a i‖ := by
  have hscaled := ha.mul_left ‖(∑' j, a j)⁻¹‖
  simpa [normalizedWeight, norm_mul] using hscaled

/-- A summable real family with nonzero total normalizes to total mass one. -/
theorem hasSum_normalizedWeight (a : ι → ℝ)
    (ha : Summable a) (hZ : (∑' i, a i) ≠ 0) :
    HasSum (normalizedWeight a) 1 := by
  have hscaled := ha.hasSum.mul_left (∑' i, a i)⁻¹
  rw [inv_mul_cancel₀ hZ] at hscaled
  exact hscaled

/-- Normalization of a nonnegative family remains nonnegative. -/
theorem normalizedWeight_nonneg (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    0 ≤ normalizedWeight a i :=
  mul_nonneg (inv_nonneg.mpr (tsum_nonneg ha)) (ha i)

/-- Each normalized nonnegative weight is at most one when the total is positive. -/
theorem normalizedWeight_le_one (a : ι → ℝ) (ha : Summable a)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hZ : 0 < ∑' i, a i) (i : ι) :
    normalizedWeight a i ≤ 1 := by
  have hs := hasSum_normalizedWeight a ha hZ.ne'
  have hle := hs.summable.le_tsum i (fun j _ => normalizedWeight_nonneg a ha_nonneg j)
  rwa [hs.tsum_eq] at hle

end Real
