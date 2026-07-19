import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock

set_option linter.style.header false

/-!
# An abstract normalized linear functional on operators

The finite-temperature Bloch–de Dominicis induction (`notes/roadmaps/second-quantization.md`)
should not itself see whether the underlying weighted expectation is a `Finset.sum`
(`Common.normalizedWeightedDiagonal`, `WeightedDiagonalFunctional.lean`, finite occupation-state
type) or, later, a `tsum` (bosonic occupation states are infinite even for a finite mode set:
`Occupation Mode := Mode →₀ ℕ`). `NormalizedOperatorFunctional Config` packages the base algebraic
shape both are expected to share — `ℂ`-linear in the operator argument, and the identity operator
evaluating to `1` — as a `LinearMap` from operators to `ℂ`.

**This is only the base linear-functional layer, not by itself enough for the Bloch–de Dominicis
identity.** Linearity and `eval id = 1` alone do not force a 4-point functional to factorize into a
pairing sum of 2-point ones — an arbitrary nonzero-total-weight complex weight already
instantiates this interface (`WeightedDiagonalFunctional.lean`'s
`normalizedWeightedDiagonalFunctional`) without any such recurrence holding for it. The Bloch–de
Dominicis theorem will need at least one further structure built *on top of* this one — e.g. a
quasifree/Gaussian pairing recursion, or a thermal exchange relation tied to a genuine free Gibbs
weight — as a separate, later addition, not part of this base interface.

This file depends only on `AlgebraicFock`, deliberately not on any concrete weighted-expectation
backend (finite-sum or `tsum`): those backends depend on this interface, not the other way around,
so a future bosonic `tsum` instantiation does not pull in the finite `[Fintype Config]` backend.

**No physical claim beyond linearity and normalization.** A `NormalizedOperatorFunctional` need not
be positive, real-valued (even against a Hermitian operator), diagonal in any particular basis, or
a genuine Gibbs-state expectation — those additional properties, where needed, are separate
hypotheses or separate extending structures, not part of this interface.
-/

namespace SecondQuantization
namespace Common

/-- **A `ℂ`-linear, identity-normalized functional** on operators over an occupation-state type
`Config`: a `LinearMap` from `AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config` to `ℂ` sending the
identity operator to `1`. See the module docstring for what this interface does *not* yet claim. -/
structure NormalizedOperatorFunctional (Config : Type*) where
  /-- The functional itself, as a linear map on operators. -/
  toLinearMap : (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ
  /-- The identity operator evaluates to `1`. -/
  map_id : toLinearMap (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1

namespace NormalizedOperatorFunctional

variable {Config : Type*}

noncomputable instance : CoeFun (NormalizedOperatorFunctional Config)
    (fun _ => (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) → ℂ) :=
  ⟨fun F => F.toLinearMap⟩

@[simp]
theorem toLinearMap_apply (F : NormalizedOperatorFunctional Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F.toLinearMap A = F A := rfl

theorem map_add (F : NormalizedOperatorFunctional Config)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F (A + B) = F A + F B :=
  F.toLinearMap.map_add A B

theorem map_smul (F : NormalizedOperatorFunctional Config) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    F (c • A) = c * F A := by
  have h := F.toLinearMap.map_smul c A
  simp only [smul_eq_mul] at h
  exact h

@[simp]
theorem map_zero (F : NormalizedOperatorFunctional Config) : F 0 = 0 :=
  F.toLinearMap.map_zero

theorem map_neg (F : NormalizedOperatorFunctional Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F (-A) = -F A :=
  F.toLinearMap.map_neg A

theorem map_sub (F : NormalizedOperatorFunctional Config)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : F (A - B) = F A - F B :=
  F.toLinearMap.map_sub A B

end NormalizedOperatorFunctional
end Common
end SecondQuantization
