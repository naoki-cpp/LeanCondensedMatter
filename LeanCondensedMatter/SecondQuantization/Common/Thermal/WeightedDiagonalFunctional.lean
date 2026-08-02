import LeanCondensedMatter.SecondQuantization.Common.Thermal.DiagonalTrace

set_option linter.style.header false

/-!
# Finite weighted diagonal formulas

Coordinate formulas on a finite occupation-state type `Config`. This module owns ordinary finite
traces, weighted traces, total weights, and normalized weighted diagonal sums. Generic matrix
coefficient and summability-aware `tsum` trace infrastructure lives in `DiagonalTrace.lean`.

The weight `w : Config → ℂ` is arbitrary. Consequently, `normalizedWeightedDiagonal` is only a raw
coordinate functional here; it becomes a physical Gibbs expectation only after specializing to
positive Boltzmann weights and relating the result to a normalized density operator.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-! ## Finite traces -/

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. -/
noncomputable def traceFock (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, matrixCoeff A n n

/-- **`matrixCoeff` under composition is ordinary matrix multiplication**,
`(AB)_{mn} = Σₖ A_{mk} B_{kn}` over all of a finite `Config`. -/
theorem matrixCoeff_comp (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑ k : Config, matrixCoeff A m k * matrixCoeff B k n := by
  rw [matrixCoeff_comp_support]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hz : matrixCoeff B k n = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.mpr h)
  rw [hz, mul_zero]

/-- The finite trace is cyclic under a two-operator swap, `Tr[AB] = Tr[BA]`. -/
theorem traceFock_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A.comp B) = traceFock (B.comp A) := by
  simp only [traceFock, matrixCoeff_comp]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- `traceFock` is linear in its operator argument: scaling. -/
theorem traceFock_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (c • A) = c * traceFock A := by
  simp only [traceFock, matrixCoeff_smul, Finset.mul_sum]

/-- `traceFock` is linear in its operator argument: addition. -/
theorem traceFock_add (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A + B) = traceFock A + traceFock B := by
  simp only [traceFock, matrixCoeff_add]
  exact Finset.sum_add_distrib

/-! ## Weighted coordinate sums -/

/-- **The weighted trace**, `Tr_w A := Σₙ w(n) ⟨n| A |n⟩`. -/
noncomputable def weightedTrace (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, w n * matrixCoeff A n n

/-- **The total weight**, `weightSum(w) := ∑ₙ w(n)`. -/
noncomputable def weightSum (w : Config → ℂ) : ℂ :=
  ∑ n : Config, w n

/-- **The normalized weighted diagonal coordinate functional**,
`Tr_w(A) / weightSum(w)`. No positivity or physical-state interpretation is implied for arbitrary
complex weights. -/
noncomputable def normalizedWeightedDiagonal (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  weightedTrace w A / weightSum w

/-! ## Linearity -/

theorem weightedTrace_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simp only [weightedTrace, matrixCoeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem weightedTrace_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B := by
  simp only [weightedTrace, matrixCoeff_add, mul_add]
  exact Finset.sum_add_distrib

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

/-- The normalized weighted diagonal functional vanishes on the zero operator. -/
theorem normalizedWeightedDiagonal_zero (w : Config → ℂ) :
    normalizedWeightedDiagonal w (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
  have h := normalizedWeightedDiagonal_smul (0 : ℂ) w
    (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
  simpa using h

/-! ## Identity and diagonal operators -/

@[simp]
theorem traceFock_id : traceFock (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) =
    (Fintype.card Config : ℂ) := by
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [traceFock, h]

/-- The weighted trace of the identity is the total weight. -/
theorem weightedTrace_id (w : Config → ℂ) :
    weightedTrace w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = weightSum w := by
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [weightedTrace, weightSum, h]

/-- The normalized weighted diagonal of the identity is one when the total weight is nonzero. -/
theorem normalizedWeightedDiagonal_id (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = 1 := by
  rw [normalizedWeightedDiagonal, weightedTrace_id, div_self hw]

/-- The weighted trace of a diagonal operator is the weighted sum of its eigenvalues. -/
theorem weightedTrace_diagonalOperator (w a : Config → ℂ) :
    weightedTrace w (diagonalOperator a) = ∑ n : Config, w n * a n := by
  simp [weightedTrace, matrixCoeff_diagonalOperator]

/-- Coordinate formula for the normalized weighted diagonal of a diagonal operator. -/
theorem normalizedWeightedDiagonal_diagonalOperator (w a : Config → ℂ) :
    normalizedWeightedDiagonal w (diagonalOperator a) =
      (∑ n : Config, w n * a n) / weightSum w := by
  rw [normalizedWeightedDiagonal, weightedTrace_diagonalOperator]

/-! ## Linear-map bundle -/

/-- `normalizedWeightedDiagonal w`, bundled as a `LinearMap` for coordinate proof reuse. -/
noncomputable def normalizedWeightedDiagonalLinearMap (w : Config → ℂ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ where
  toFun := normalizedWeightedDiagonal w
  map_add' := normalizedWeightedDiagonal_add w
  map_smul' := fun c A => normalizedWeightedDiagonal_smul c w A

@[simp]
theorem normalizedWeightedDiagonalLinearMap_apply (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonalLinearMap w A = normalizedWeightedDiagonal w A := rfl

end Common
end SecondQuantization
