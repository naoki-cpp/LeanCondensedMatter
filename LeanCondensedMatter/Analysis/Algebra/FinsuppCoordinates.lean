import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Coordinates of linear maps on free modules

Finite-support coordinate expansions for linear maps between free modules,
without any restriction on the cardinalities of the index types. Iterated column supports
bound the reachable indices under successive operator applications.
-/

namespace Finsupp

/-- A linear operator acts coordinatewise by its matrix coefficients on any finite set
containing the input vector's support. -/
theorem linearMap_apply_eq_finsetSum_of_support_subset
    {R ι κ : Type*} [CommSemiring R]
    (A : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (x : ι →₀ R) (S : Finset ι) (hx : x.support ⊆ S) (m : κ) :
    A x m = ∑ k ∈ S, A (Finsupp.single k 1) m * x k := by
  classical
  calc
    A x m = ∑ k ∈ x.support, A (Finsupp.single k 1) m * x k := by
      have h := congrArg (fun T : (ι →₀ R) →ₗ[R] (κ →₀ R) => T x m)
        ((Finsupp.lift (κ →₀ R) R ι).apply_symm_apply A).symm
      simpa only [Finsupp.lift_apply, Finsupp.lift_symm_apply, Finsupp.sum,
        Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm] using h
    _ = ∑ k ∈ S, A (Finsupp.single k 1) m * x k := by
      apply Finset.sum_subset hx
      intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk, mul_zero]


section

variable {R ι : Type*} [CommSemiring R]

/-- Classical decidable equality used only to construct finite reachable supports. -/
noncomputable local instance indexDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Indices reachable from `n` after exactly `order` applications of the linear operator
`V`, with possible cancellation deliberately ignored. -/
noncomputable def reachableSupport
    (V : (ι →₀ R) →ₗ[R] (ι →₀ R)) : ℕ → ι → Finset ι
  | 0, n => {n}
  | order + 1, n =>
      (reachableSupport V order n).biUnion fun k => (V (Finsupp.single k 1)).support

@[simp]
theorem reachableSupport_succ
    (V : (ι →₀ R) →ₗ[R] (ι →₀ R)) (order : ℕ) (n : ι) :
    reachableSupport V (order + 1) n =
      (reachableSupport V order n).biUnion fun k => (V (Finsupp.single k 1)).support := rfl

/-- If the matrix columns of `A` are supported in the corresponding columns of `B`,
applying `A` advances the support bound for `B` by one step. -/
theorem support_apply_subset_reachableSupport_succ
    (A B : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (hAB : ∀ k, (A (Finsupp.single k 1)).support ⊆ (B (Finsupp.single k 1)).support)
    (order : ℕ) (n : ι) (x : ι →₀ R)
    (hx : x.support ⊆ reachableSupport B order n) :
    (A x).support ⊆ reachableSupport B (order + 1) n := by
  intro m hm
  rw [Finsupp.mem_support_iff,
    linearMap_apply_eq_finsetSum_of_support_subset A x x.support (subset_refl _) m] at hm
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [reachableSupport_succ, Finset.mem_biUnion]
  refine ⟨k, hx hk, hAB k (Finsupp.mem_support_iff.mpr ?_)⟩
  intro hz
  exact hne (by rw [hz, zero_mul])

end

end Finsupp
