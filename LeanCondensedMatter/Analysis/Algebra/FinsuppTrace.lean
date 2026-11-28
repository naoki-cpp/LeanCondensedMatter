import LeanCondensedMatter.Analysis.Algebra.FinsuppCoordinates
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option linter.style.header false

/-!
# Diagonal series of free-module endomorphisms

Coordinate expansions and cyclicity of the diagonal series, with explicit
summability assumptions and no Hilbert-space structure.
-/

namespace Finsupp

variable {R ι κ : Type*} [NormedField R]

/-- The coordinate expansion can be written as an infinite sum because the input has finite support. -/
theorem linearMap_apply_eq_tsum (A : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (x : ι →₀ R) (m : κ) :
    A x m = ∑' k, A (Finsupp.single k 1) m * x k := by
  rw [linearMap_apply_eq_finsetSum_of_support_subset A x x.support (subset_refl _) m]
  exact ((hasSum_sum_of_ne_finset_zero (s := x.support)
    (fun k hk => by rw [Finsupp.notMem_support_iff.mp hk, mul_zero])).tsum_eq).symm

variable [CompleteSpace R]

/-- The diagonal series of a composite is invariant under swapping the two factors
when the double series is summable. -/
theorem tsum_diagonal_comp_comm (A B : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (h : Summable (Function.uncurry
      (fun n k => A (Finsupp.single k 1) n * B (Finsupp.single n 1) k))) :
    (∑' n, (A.comp B) (Finsupp.single n 1) n) =
      ∑' n, (B.comp A) (Finsupp.single n 1) n := by
  calc
    _ = ∑' n, ∑' k, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
      tsum_congr fun n => linearMap_apply_eq_tsum A (B (Finsupp.single n 1)) n
    _ = ∑' k, ∑' n, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
      h.tsum_comm.symm
    _ = _ := tsum_congr fun k => by
      change _ = B (A (Finsupp.single k 1)) k
      rw [linearMap_apply_eq_tsum]
      exact tsum_congr fun n => mul_comm _ _

/-- Summability of the double series implies summability of the composite's diagonal. -/
theorem summable_diagonal_comp_of_summable_uncurry
    (A B : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (h : Summable (Function.uncurry
      (fun n k => A (Finsupp.single k 1) n * B (Finsupp.single n 1) k))) :
    Summable (fun n => (A.comp B) (Finsupp.single n 1) n) := by
  have hrow : (fun n => (A.comp B) (Finsupp.single n 1) n) =
      fun n => ∑' k, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
    funext fun n => linearMap_apply_eq_tsum A (B (Finsupp.single n 1)) n
  rw [hrow]
  exact h.prod

end Finsupp
