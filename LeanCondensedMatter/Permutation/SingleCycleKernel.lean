import LeanCondensedMatter.Permutation.ConnectedDecomposition

set_option linter.style.header false

/-!
# Single-cycle kernel sums

This file starts W3 of the exchange/cumulant backend by separating the universal
`ζ ^ (|S| - 1)` weight of a connected permutation from the kernel-dependent sum over
single-orbit permutations.

The result is deliberately coefficient-level. Matrix traces, cyclic rotation, formal power
series, and formal logarithms belong to later layers built on this boundary.
-/

namespace Combinatorics

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The pure kernel sum over single-orbit permutations on `S`.

It is defined as the connected contribution at exchange weight `1`, so W3 reuses the W2 backend
without exposing its private connected-permutation representation. -/
noncomputable def singleCycleKernelSum {R : Type*} [CommSemiring R]
    (K : α → α → R) (S : Finset α) : R :=
  singleCycleContribution (1 : R) K S

/-- A connected permutation on `S` carries the common exchange factor `ζ ^ (|S| - 1)`.

This is the coefficient-level W3 boundary: all `ζ` dependence factors out before any cyclic-trace
or formal-power-series argument is introduced. -/
theorem singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum
    {R : Type*} [CommSemiring R] (ζ : R) (K : α → α → R) (S : Finset α) :
    singleCycleContribution ζ K S =
      ζ ^ (S.card - 1) * singleCycleKernelSum K S := by
  classical
  rw [singleCycleKernelSum, singleCycleContribution, singleCycleContribution,
    MultiplicativeWeight.connectedContribution, MultiplicativeWeight.connectedContribution,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  change ζ ^ (S.card - 1) * _ =
    ζ ^ (S.card - 1) * (1 ^ (S.card - 1) * _)
  simp

/-- Fixed-cardinality form of the connected single-cycle kernel theorem. -/
theorem singleCycleContribution_of_card_eq
    {R : Type*} [CommSemiring R] (ζ : R) (K : α → α → R) (S : Finset α)
    (m : ℕ) (hcard : S.card = m) :
    singleCycleContribution ζ K S =
      ζ ^ (m - 1) * singleCycleKernelSum K S := by
  rw [singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum, hcard]

/-- Finiteness of full-cycle permutations for the semantic W3 endpoint. -/
noncomputable local instance singleCycleKernelFullCycleFintype :
    Fintype {σ : Equiv.Perm α // σ.IsCycleOn (Set.univ : Set α)} :=
  Fintype.ofFinite _

/-- On the full finite index type, the pure connected kernel is the direct sum over permutations
that are a single cycle on the whole type. This is the exchange-weight-one specialization of the
generic connected-contribution endpoint owned by W2. -/
theorem singleCycleKernelSum_univ_eq_sum_isCycleOn
    {R : Type*} [CommSemiring R] (K : α → α → R) :
    singleCycleKernelSum K univ =
      ∑ σ : {σ : Equiv.Perm α // σ.IsCycleOn (Set.univ : Set α)},
        ∏ i : α, K i (σ.1 i) := by
  simpa [singleCycleKernelSum] using
    (singleCycleContribution_univ_eq_sum_isCycleOn (α := α) (1 : R) K)

end Combinatorics
