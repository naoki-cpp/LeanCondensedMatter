import LeanCondensedMatter.Combinatorics.Cumulant.Inversion
import LeanCondensedMatter.Permutation.ConnectedDecomposition

set_option linter.style.header false

/-!
# Cumulant inversion of the ζ-weighted permutation moment

The permutation backend and its moment decomposition are semiring-generic. This module adds only the
Möbius-inversion endpoint, keeping the low-level permutation and perfect-pairing layers independent
of the inversion machinery.
-/

namespace Combinatorics

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Möbius inversion of the permutation-sum family recovers the single-cycle contribution. -/
theorem cumulantFromMoment_permutationSum_eq_singleCycleContribution
    {R : Type*} [CommRing R] (ζ : R) (K : α → α → R)
    {S : Finset α} (hS : S ≠ ∅) :
    Finpartition.cumulantFromMoment (permutationSum ζ K) S =
      singleCycleContribution ζ K S := by
  have h := Finpartition.cumulantFromMoment_momentFromCumulant
    (singleCycleContribution ζ K) (S := S) hS
  have hfun : Finpartition.momentFromCumulant (singleCycleContribution ζ K) =
      permutationSum ζ K :=
    funext fun T => (permutationSum_eq_momentFromCumulant ζ K T).symm
  rwa [hfun] at h

end Combinatorics
