import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteWeightedTrace

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

/-- **The normalized weighted diagonal coordinate functional**,
`Tr_w(A) / weightSum(w)`, bundled as a complex-linear functional of `A`. No positivity or
physical-state interpretation is implied for arbitrary complex weights. -/
noncomputable def normalizedWeightedDiagonal (w : Config → ℂ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ where
  toFun A := weightedTrace w A / weightSum w
  map_add' A B := by
    rw [weightedTrace_add, add_div]
  map_smul' c A := by
    rw [weightedTrace_smul]
    change c * weightedTrace w A / weightSum w = c * (weightedTrace w A / weightSum w)
    exact mul_div_assoc c (weightedTrace w A) (weightSum w)

/-! ## Linearity -/

@[simp]
theorem normalizedWeightedDiagonal_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (c • A) = c * normalizedWeightedDiagonal w A := by
  simpa [smul_eq_mul] using (normalizedWeightedDiagonal w).map_smul c A

@[simp]
theorem normalizedWeightedDiagonal_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A + B) =
      normalizedWeightedDiagonal w A + normalizedWeightedDiagonal w B :=
  (normalizedWeightedDiagonal w).map_add A B

@[simp]
theorem normalizedWeightedDiagonal_neg (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (-A) = -normalizedWeightedDiagonal w A :=
  (normalizedWeightedDiagonal w).map_neg A

@[simp]
theorem normalizedWeightedDiagonal_sub (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A - B) =
      normalizedWeightedDiagonal w A - normalizedWeightedDiagonal w B :=
  (normalizedWeightedDiagonal w).map_sub A B

/-- The normalized weighted diagonal functional vanishes on the zero operator. -/
@[simp]
theorem normalizedWeightedDiagonal_zero (w : Config → ℂ) :
    normalizedWeightedDiagonal w (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 :=
  (normalizedWeightedDiagonal w).map_zero

/-! ## Identity and diagonal operators -/

/-- The normalized weighted diagonal of the identity is one when the total weight is nonzero. -/
theorem normalizedWeightedDiagonal_id (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = 1 := by
  change weightedTrace w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) / weightSum w = 1
  rw [weightedTrace_id, div_self hw]

/-- Coordinate formula for the normalized weighted diagonal of a diagonal operator. -/
theorem normalizedWeightedDiagonal_diagonalOperator (w a : Config → ℂ) :
    normalizedWeightedDiagonal w (diagonalOperator a) =
      (∑ n : Config, w n * a n) / weightSum w := by
  change weightedTrace w (diagonalOperator a) / weightSum w = _
  rw [weightedTrace_diagonalOperator]

end Common
end SecondQuantization
