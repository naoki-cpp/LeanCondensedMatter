import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteWeightedTrace

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
`Tr_w(A) / weightSum(w)`. No positivity or physical-state interpretation is implied for arbitrary
complex weights. -/
noncomputable def normalizedWeightedDiagonal (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  weightedTrace w A / weightSum w

/-! ## Linearity -/

theorem normalizedWeightedDiagonal_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (c • A) = c * normalizedWeightedDiagonal w A := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, weightedTrace_smul, mul_div_assoc]

theorem normalizedWeightedDiagonal_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A + B) =
      normalizedWeightedDiagonal w A + normalizedWeightedDiagonal w B := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    weightedTrace_add, add_div]

theorem normalizedWeightedDiagonal_neg (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (-A) = -normalizedWeightedDiagonal w A := by
  rw [show (-A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, normalizedWeightedDiagonal_smul, neg_one_mul]

theorem normalizedWeightedDiagonal_sub (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A - B) =
      normalizedWeightedDiagonal w A - normalizedWeightedDiagonal w B := by
  change normalizedWeightedDiagonal w (A + -B) =
    normalizedWeightedDiagonal w A + -normalizedWeightedDiagonal w B
  rw [normalizedWeightedDiagonal_add, normalizedWeightedDiagonal_neg]

/-! ## Identity and diagonal operators -/

/-- The normalized weighted diagonal of the identity is one when the total weight is nonzero. -/
theorem normalizedWeightedDiagonal_id (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = 1 := by
  rw [normalizedWeightedDiagonal, weightedTrace_id, div_self hw]

/-- Coordinate formula for the normalized weighted diagonal of a diagonal operator. -/
theorem normalizedWeightedDiagonal_diagonalOperator (w a : Config → ℂ) :
    normalizedWeightedDiagonal w (diagonalOperator a) =
      (∑ n : Config, w n * a n) / weightSum w := by
  rw [normalizedWeightedDiagonal, weightedTrace_diagonalOperator]

end Common
end SecondQuantization
