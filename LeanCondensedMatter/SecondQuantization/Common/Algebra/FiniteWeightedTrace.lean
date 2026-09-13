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

variable {Config : Type*}

/-! ## Finite traces -/

/-- **The Fock-space trace** as the canonical linear trace on the finite free algebraic Fock
space. Its occupation-basis coordinate formula is `traceFock_eq_sum_matrixCoeff`. -/
@[nolint unusedArguments]
noncomputable def traceFock [Fintype Config] :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ (AlgebraicFock Config)

/-- Coordinate formula for the canonical trace in the occupation basis. -/
theorem traceFock_eq_sum_matrixCoeff [Fintype Config]
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock A = ∑ n : Config, matrixCoeff A n n := by
  classical
  change LinearMap.trace ℂ (AlgebraicFock Config) A = _
  rw [LinearMap.trace_eq_matrix_trace ℂ
    (Finsupp.basisSingleOne : Module.Basis Config ℂ (AlgebraicFock Config))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, matrixCoeff, basisState, Finsupp.basisSingleOne]

/-- The finite trace is cyclic under a two-operator swap, `Tr[AB] = Tr[BA]`. -/
theorem traceFock_comp_comm [Fintype Config]
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A.comp B) = traceFock (B.comp A) := by
  change LinearMap.trace ℂ (AlgebraicFock Config) (A.comp B) =
    LinearMap.trace ℂ (AlgebraicFock Config) (B.comp A)
  simpa only [Module.End.mul_eq_comp] using (LinearMap.trace_mul_comm ℂ A B)

/-! ## Weighted coordinate sums -/

variable [Fintype Config]

/-- **The weighted trace** as the finite linear combination of diagonal matrix-coefficient
functionals, `Tr_w A := Σₙ w(n) ⟨n| A |n⟩`. -/
noncomputable def weightedTrace (w : Config → ℂ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  ∑ n : Config, w n • matrixCoeffLinear n n

/-- Coordinate formula for the weighted trace. -/
theorem weightedTrace_eq_sum_matrixCoeff (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w A = ∑ n : Config, w n * matrixCoeff A n n := by
  simp [weightedTrace]

/-- **The total weight**, `weightSum(w) := ∑ₙ w(n)`. -/
noncomputable def weightSum (w : Config → ℂ) : ℂ :=
  ∑ n : Config, w n

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
  rw [weightedTrace_eq_sum_matrixCoeff]
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [weightSum, h]

/-- The weighted trace of a diagonal operator is the weighted sum of its eigenvalues. -/
theorem weightedTrace_diagonalOperator (w a : Config → ℂ) :
    weightedTrace w (diagonalOperator a) = ∑ n : Config, w n * a n := by
  rw [weightedTrace_eq_sum_matrixCoeff]
  simp [matrixCoeff_diagonalOperator]

end Common
end SecondQuantization
