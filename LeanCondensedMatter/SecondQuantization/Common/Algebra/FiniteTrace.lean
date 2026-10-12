import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import Mathlib.LinearAlgebra.Trace

set_option linter.style.header false

/-!
# Finite traces and weight sums

For a finite occupation-state type `Config`, this module owns the canonical linear trace on
algebraic Fock endomorphisms, its occupation-basis coordinate formula, and finite total weights.

`weightSum` is an unnormalized scalar coordinate sum, not a Gibbs partition function or state
until the weights are specialized and normalization is justified.
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

/-! ## Finite scalar weight sums -/

variable [Fintype Config]

/-- **The total weight**, `weightSum(w) := ∑ₙ w(n)`. -/
noncomputable def weightSum (w : Config → ℂ) : ℂ :=
  ∑ n : Config, w n

/-! ## Trace of the identity -/

@[simp]
theorem traceFock_id : traceFock (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) =
    (Fintype.card Config : ℂ) := by
  rw [traceFock_eq_sum_matrixCoeff]
  simp [matrixCoeff_id]

end Common
end SecondQuantization
