import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import Mathlib.LinearAlgebra.Trace

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

/-- **The Fock-space trace** as the canonical linear trace on the finite free algebraic Fock
space. Its occupation-basis coordinate formula is `traceFock_eq_sum_matrixCoeff`. -/
noncomputable def traceFock :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ (AlgebraicFock Config)

/-- Coordinate formula for the canonical trace in the occupation basis. -/
theorem traceFock_eq_sum_matrixCoeff
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock A = ∑ n : Config, matrixCoeff A n n := by
  classical
  change LinearMap.trace ℂ (AlgebraicFock Config) A = _
  rw [LinearMap.trace_eq_matrix_trace ℂ
    (Finsupp.basisSingleOne : Basis Config ℂ (AlgebraicFock Config))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, matrixCoeff, basisState, Finsupp.basisSingleOne]

/-- The finite trace is cyclic under a two-operator swap, `Tr[AB] = Tr[BA]`. -/
theorem traceFock_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A.comp B) = traceFock (B.comp A) := by
  change LinearMap.trace ℂ (AlgebraicFock Config) (A.comp B) =
    LinearMap.trace ℂ (AlgebraicFock Config) (B.comp A)
  simpa only [Module.End.mul_eq_comp] using (LinearMap.trace_mul_comm ℂ A B)

/-- `traceFock` is linear in its operator argument: scaling. -/
theorem traceFock_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (c • A) = c * traceFock A := by
  simpa only [smul_eq_mul] using (traceFock (Config := Config)).map_smul c A

/-- `traceFock` is linear in its operator argument: addition. -/
theorem traceFock_add (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A + B) = traceFock A + traceFock B :=
  (traceFock (Config := Config)).map_add A B

/-! ## Weighted coordinate sums -/

/-- **The weighted trace** as a linear functional on endomorphisms,
`Tr_w A := Σₙ w(n) ⟨n| A |n⟩`. -/
noncomputable def weightedTrace (w : Config → ℂ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ where
  toFun := fun A => ∑ n : Config, w n * matrixCoeff A n n
  map_add' := by
    intro A B
    simp only [matrixCoeff_add, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    simp only [matrixCoeff_smul, Finset.mul_sum, smul_eq_mul, RingHom.id_apply]
    exact Finset.sum_congr rfl fun n _ => by ring

/-- **The total weight**, `weightSum(w) := ∑ₙ w(n)`. -/
noncomputable def weightSum (w : Config → ℂ) : ℂ :=
  ∑ n : Config, w n

/-- `weightedTrace` is linear in its operator argument: scaling. -/
theorem weightedTrace_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simpa only [smul_eq_mul] using (weightedTrace w).map_smul c A

/-- `weightedTrace` is linear in its operator argument: addition. -/
theorem weightedTrace_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B :=
  (weightedTrace w).map_add A B

/-! ## Identity and diagonal operators -/

@[simp]
theorem traceFock_id : traceFock (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) =
    (Fintype.card Config : ℂ) := by
  rw [traceFock_eq_sum_matrixCoeff]
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [h]

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
