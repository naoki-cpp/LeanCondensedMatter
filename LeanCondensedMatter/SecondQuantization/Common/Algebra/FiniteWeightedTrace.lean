import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace

set_option linter.style.header false

/-!
# Finite traces and weighted coordinate sums

Coordinate formulas on a finite occupation-state type `Config`. This module owns ordinary finite
traces, weighted traces, and total weights. Normalized weighted diagonal formulas live separately
in `WeightedDiagonalFunctional.lean`.

The weight `w : Config → ℂ` is arbitrary, so `weightedTrace` and `weightSum` are raw coordinate
quantities. A physical Gibbs interpretation only appears after specialization to positive
Boltzmann weights and comparison with a normalized density operator.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-! ## Finite traces -/

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. -/
noncomputable def traceFock (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, matrixCoeff A n n

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

/-- `weightedTrace` is linear in its operator argument: scaling. -/
theorem weightedTrace_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simp only [weightedTrace, matrixCoeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- `weightedTrace` is linear in its operator argument: addition. -/
theorem weightedTrace_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B := by
  simp only [weightedTrace, matrixCoeff_add, mul_add]
  exact Finset.sum_add_distrib

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

/-- The weighted trace of a diagonal operator is the weighted sum of its eigenvalues. -/
theorem weightedTrace_diagonalOperator (w a : Config → ℂ) :
    weightedTrace w (diagonalOperator a) = ∑ n : Config, w n * a n := by
  simp [weightedTrace, matrixCoeff_diagonalOperator]

end Common
end SecondQuantization
