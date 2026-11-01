import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import Mathlib.Algebra.BigOperators.Finsupp.Basic

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

/-- Classical decidable equality used only to construct finite reachable supports. -/
noncomputable local instance configDecidableEq : DecidableEq Config := Classical.decEq Config

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

/-- Applying an interaction-picture insertion to a vector supported at one reachable order produces
only configurations reachable at the next order. -/
theorem support_interactionPicture_apply_subset_reachableSupport_succ
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (order : ℕ) (n : Config) (x : AlgebraicFock Config)
    (hx : x.support ⊆ reachableSupport V order n) :
    (interactionPicture energy V τ x).support ⊆ reachableSupport V (order + 1) n := by
  have hxRep : x = ∑ k ∈ x.support, x k • basisState k :=
    eq_sum_smul_basisState x
  have hImage :
      interactionPicture energy V τ x =
        ∑ k ∈ x.support, x k • interactionPicture energy V τ (basisState k) := by
    conv_lhs => rw [hxRep, map_sum]
    simp only [map_smul]
  intro m hm
  rw [reachableSupport_succ, Finset.mem_biUnion]
  rw [hImage] at hm
  obtain ⟨k, hk, hmk⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hm)
  exact ⟨k, hx hk,
    support_interactionPicture_basisState_subset energy V τ k
      (Finsupp.support_smul hmk)⟩

end Common
end SecondQuantization
