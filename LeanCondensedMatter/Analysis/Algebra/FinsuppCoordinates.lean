import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Coordinates of linear maps on free modules

Finite-support coordinate expansions for linear maps between free modules,
without any restriction on the cardinalities of the index types.
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
    A x m = A (∑ k ∈ x.support, x k • Finsupp.single k 1) m := by
      have hrep : x = ∑ k ∈ x.support, x k • Finsupp.single k 1 := by
        simpa only [Finsupp.sum, Finsupp.smul_single_one] using (Finsupp.sum_single x).symm
      rw [← hrep]
    _ = ∑ k ∈ x.support, A (Finsupp.single k 1) m * x k := by
      rw [map_sum, Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, Finsupp.smul_apply]
      change x k * A (Finsupp.single k 1) m = A (Finsupp.single k 1) m * x k
      exact mul_comm _ _
    _ = ∑ k ∈ S, A (Finsupp.single k 1) m * x k := by
      apply Finset.sum_subset hx
      intro k _ hk
      have hz : x k = 0 := by
        by_contra hn
        exact hk (Finsupp.mem_support_iff.mpr hn)
      rw [hz, mul_zero]

end Finsupp
