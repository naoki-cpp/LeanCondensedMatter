import LeanCondensedMatter.SecondQuantization.Common.Perturbation.MatrixCoefficientDyson

set_option linter.style.header false

/-!
# Finite reachable supports for algebraic Dyson coefficients

For an algebraic-Fock operator `V`, every basis image `V (basisState n)` has finite support by
construction. Iterating those finite supports gives a finite set of configurations reachable from a
fixed input after any fixed number of interaction insertions, even when the ambient configuration
type is infinite.

This file records only that algebraic support boundary. It does not define an operator-valued
integral, assert boundedness, or claim convergence of the infinite Dyson series.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

noncomputable local instance : DecidableEq Config := Classical.decEq Config

/-- Configurations reachable from `n` after exactly `order` applications of the algebraic operator
`V`, with possible cancellation deliberately ignored. -/
noncomputable def reachableSupport
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℕ → Config → Finset Config
  | 0, n => {n}
  | order + 1, n =>
      (reachableSupport V order n).biUnion fun k => (V (basisState k)).support

@[simp]
theorem reachableSupport_zero
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) :
    reachableSupport V 0 n = {n} := rfl

@[simp]
theorem reachableSupport_succ
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (n : Config) :
    reachableSupport V (order + 1) n =
      (reachableSupport V order n).biUnion fun k => (V (basisState k)).support := rfl

/-- Membership in the next reachable support is witnessed by an intermediate configuration in the
previous support and a nonzero matrix column of `V`. -/
theorem mem_reachableSupport_succ_iff
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (m n : Config) :
    m ∈ reachableSupport V (order + 1) n ↔
      ∃ k ∈ reachableSupport V order n, m ∈ (V (basisState k)).support := by
  simp [reachableSupport]

/-- The first reachable support is exactly large enough to contain the support used by the
first-order infinite-configuration Dyson construction. -/
theorem support_basisImage_subset_reachableSupport_one
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) :
    (V (basisState n)).support ⊆ reachableSupport V 1 n := by
  intro m hm
  simp [reachableSupport, hm]

end Common
end SecondQuantization
