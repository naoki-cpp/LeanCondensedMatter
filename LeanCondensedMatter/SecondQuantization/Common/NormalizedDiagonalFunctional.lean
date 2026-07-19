import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# An abstract normalized, linear diagonal functional interface

The finite-temperature Bloch–de Dominicis induction (`notes/roadmaps/second-quantization.md`)
should not itself see whether the underlying weighted expectation is a `Finset.sum`
(`Common.normalizedWeightedDiagonal`, finite occupation-state type) or, later, a `tsum`
(bosonic occupation states are infinite even for a finite mode set: `Occupation Mode := Mode →₀
ℕ`). `NormalizedDiagonalFunctional Config` packages exactly the algebraic shape the induction
needs — linearity in the operator argument, and the identity operator evaluating to `1` — without
committing to either summation mechanism.

This file only introduces the interface and the fermionic finite-sum instantiation
(`normalizedWeightedDiagonalFunctional`, built directly from `Common.normalizedWeightedDiagonal`'s
already-proved `_add`/`_smul`/`_id` facts). It does **not** yet: build a bosonic `tsum`-based
instantiation (a separate, summability-aware construction — not an instantiation of the finite-sum
one, since `Occupation Mode` doesn't satisfy `[Fintype Config]`); connect this interface to
`ExchangeAlgebra` or the pairing combinatorics; or state any Bloch–de Dominicis identity. Those are
separate future work.

**No physical claim beyond linearity and normalization.** As with `normalizedWeightedDiagonal`
itself, a `NormalizedDiagonalFunctional` need not be positive, real-valued (even against a
Hermitian operator), or a genuine Gibbs-state expectation — those additional properties, where
needed, are separate hypotheses a caller supplies, not part of this interface.
-/

namespace SecondQuantization
namespace Common

/-- **A bundled, ℂ-linear, identity-normalized diagonal functional** on operators over an
occupation-state type `Config`: additive and homogeneous in the operator argument, and sending the
identity operator to `1`. Both the finite-sum `normalizedWeightedDiagonal` (via
`normalizedWeightedDiagonalFunctional` below) and a future bosonic `tsum`-based construction are
expected to instantiate this. -/
structure NormalizedDiagonalFunctional (Config : Type*) where
  /-- The functional itself. -/
  eval : (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) → ℂ
  /-- Additivity in the operator argument. -/
  eval_add : ∀ A B, eval (A + B) = eval A + eval B
  /-- Homogeneity in the operator argument. -/
  eval_smul : ∀ (c : ℂ) A, eval (c • A) = c * eval A
  /-- The identity operator evaluates to `1`. -/
  eval_id : eval (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1

namespace NormalizedDiagonalFunctional

variable {Config : Type*} (F : NormalizedDiagonalFunctional Config)

@[simp]
theorem eval_zero : F.eval 0 = 0 := by
  have h := F.eval_smul 0 0
  simpa using h

theorem eval_neg (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F.eval (-A) = -F.eval A := by
  rw [show (-A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, F.eval_smul, neg_one_mul]

theorem eval_sub (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F.eval (A - B) = F.eval A - F.eval B := by
  rw [sub_eq_add_neg, F.eval_add, F.eval_neg, sub_eq_add_neg]

end NormalizedDiagonalFunctional

variable {Config : Type*} [Fintype Config]

/-- **The finite-sum instantiation** of `NormalizedDiagonalFunctional`, for a weight `w : Config →
ℂ` with nonzero total weight: `eval := normalizedWeightedDiagonal w`, with the three required laws
supplied directly by `normalizedWeightedDiagonal_add`/`_smul`/`_id`. -/
noncomputable def normalizedWeightedDiagonalFunctional (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    NormalizedDiagonalFunctional Config where
  eval := normalizedWeightedDiagonal w
  eval_add := normalizedWeightedDiagonal_add w
  eval_smul := fun c A => normalizedWeightedDiagonal_smul c w A
  eval_id := normalizedWeightedDiagonal_id w hw

@[simp]
theorem normalizedWeightedDiagonalFunctional_eval (w : Config → ℂ) (hw : weightSum w ≠ 0)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    (normalizedWeightedDiagonalFunctional w hw).eval A = normalizedWeightedDiagonal w A := rfl

end Common
end SecondQuantization
