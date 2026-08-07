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

/-- Membership in the next reachable support is witnessed by an intermediate configuration in the
previous support and a nonzero matrix column of `V`. -/
theorem mem_reachableSupport_succ_iff
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (m n : Config) :
    m ∈ reachableSupport V (order + 1) n ↔
      ∃ k ∈ reachableSupport V order n, m ∈ (V (basisState k)).support := by
  simp [reachableSupport]

/-- The first reachable support is exactly large enough to contain one algebraic basis image. -/
theorem support_basisImage_subset_reachableSupport_one
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) :
    (V (basisState n)).support ⊆ reachableSupport V 1 n := by
  intro m hm
  simp [reachableSupport, hm]

/-- Every first-order interaction-picture integrand is supported in the first reachable support. -/
theorem support_interactionPicture_basisState_subset_reachableSupport_one
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (n : Config) :
    (interactionPicture energy V τ (basisState n)).support ⊆ reachableSupport V 1 n :=
  (support_interactionPicture_basisState_subset energy V τ n).trans
    (support_basisImage_subset_reachableSupport_one V n)

/-- Applying an interaction-picture insertion to a vector supported at one reachable order produces
only configurations reachable at the next order. -/
theorem support_interactionPicture_apply_subset_reachableSupport_succ
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (order : ℕ) (n : Config) (x : AlgebraicFock Config)
    (hx : x.support ⊆ reachableSupport V order n) :
    (interactionPicture energy V τ x).support ⊆ reachableSupport V (order + 1) n := by
  intro m hm
  rw [mem_reachableSupport_succ_iff]
  have hxRep : x = ∑ k ∈ x.support, x k • basisState k := by
    conv_lhs => rw [← Finsupp.sum_single x]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => (Finsupp.smul_single_one k _).symm
  by_contra hnot
  have hzero : interactionPicture energy V τ x m = 0 := by
    rw [hxRep, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hkReach : k ∈ reachableSupport V order n := hx hk
    have hmk : m ∉ (interactionPicture energy V τ (basisState k)).support := by
      intro hmem
      apply hnot
      exact ⟨k, hkReach,
        support_interactionPicture_basisState_subset energy V τ k hmem⟩
    have hcol : interactionPicture energy V τ (basisState k) m = 0 :=
      Finsupp.not_mem_support_iff.mp hmk
    simp [hcol]
  exact (Finsupp.mem_support_iff.mp hm) hzero

/-- The reconstructed first Dyson basis image remains in the same first reachable support. -/
theorem support_firstDysonCoeff_basisState_subset_reachableSupport_one
    (energy : Config → ℝ) (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (τ : ℝ) (n : Config) :
    (firstDysonCoeff energy V τ (basisState n)).support ⊆ reachableSupport V 1 n :=
  (support_firstDysonCoeff_basisState_subset energy V τ n).trans
    (support_basisImage_subset_reachableSupport_one V n)

end Common
end SecondQuantization
