import LeanCondensedMatter.Analysis.NormalizedEndomorphismFunctional
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteWeightedTrace
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering

set_option linter.style.header false

/-!
# Normalized finite weighted diagonal formulas

Normalized coordinate formulas on a finite occupation-state type `Config`. The underlying finite
trace, weighted trace, and total weight are owned by `FiniteWeightedTrace.lean`.

The weight `w : Config → ℂ` is arbitrary. Consequently, `normalizedWeightedDiagonal` is only a raw
coordinate functional here; it becomes a physical Gibbs expectation only after specializing to
positive Boltzmann weights and relating the result to a normalized density operator.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The normalized weighted diagonal coordinate functional**, obtained by scaling `weightedTrace`
by the inverse total weight. No positivity or physical-state interpretation is implied for arbitrary
complex weights. -/
noncomputable def normalizedWeightedDiagonal (w : Config → ℂ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  (weightSum w)⁻¹ • weightedTrace w

/-- Coordinate formula underlying the normalized weighted diagonal functional. -/
theorem normalizedWeightedDiagonal_eq_weightedTrace_div (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w A = weightedTrace w A / weightSum w := by
  simp [normalizedWeightedDiagonal, div_eq_mul_inv, mul_comm]

/-- A normalized weighted diagonal vanishes when every diagonal matrix coefficient vanishes. -/
theorem normalizedWeightedDiagonal_eq_zero_of_matrixCoeff_self_eq_zero
    (w : Config → ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hdiag : ∀ n, matrixCoeff A n n = 0) :
    normalizedWeightedDiagonal w A = 0 := by
  rw [normalizedWeightedDiagonal_eq_weightedTrace_div, weightedTrace_eq_sum_matrixCoeff]
  simp [hdiag]

/-- Time ordering preserves vanishing when both operator orders have zero weighted diagonal. -/
theorem normalizedWeightedDiagonal_timeOrderedProduct_eq_zero
    (s : Statistics) (w : Config → ℂ) (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τA τB : ℝ) (hAB : normalizedWeightedDiagonal w (A.comp B) = 0)
    (hBA : normalizedWeightedDiagonal w (B.comp A) = 0) :
    normalizedWeightedDiagonal w (timeOrderedProduct s A B τA τB) = 0 := by
  unfold timeOrderedProduct
  split_ifs <;> simp [hAB, hBA]

/-! ## Identity and diagonal operators -/

/-- The normalized weighted diagonal of the identity is one when the total weight is nonzero. -/
theorem normalizedWeightedDiagonal_id (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = 1 := by
  rw [normalizedWeightedDiagonal_eq_weightedTrace_div, weightedTrace_id, div_self hw]

/-- The normalized weighted diagonal as a normalized endomorphism functional when its total weight
is nonzero. -/
noncomputable def normalizedWeightedDiagonalFunctional (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    NormalizedEndomorphismFunctional ℂ (AlgebraicFock Config) where
  toLinearMap := normalizedWeightedDiagonal w
  map_id := normalizedWeightedDiagonal_id w hw

/-- Coordinate formula for the normalized weighted diagonal of a diagonal operator. -/
theorem normalizedWeightedDiagonal_diagonalOperator (w a : Config → ℂ) :
    normalizedWeightedDiagonal w (diagonalOperator a) =
      (∑ n : Config, w n * a n) / weightSum w := by
  rw [normalizedWeightedDiagonal_eq_weightedTrace_div, weightedTrace_diagonalOperator]

end Common
end SecondQuantization
