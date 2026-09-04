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
  rw [show permutationSum ζ K =
      Finpartition.momentFromCumulant (singleCycleContribution ζ K) from
    funext fun T => permutationSum_eq_momentFromCumulant ζ K T]
  exact Finpartition.cumulantFromMoment_momentFromCumulant
    (singleCycleContribution ζ K) (S := S) hS

end Combinatorics
