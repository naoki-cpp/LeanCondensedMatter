import LeanCondensedMatter.Combinatorics.PermutationConnectedDecomposition

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

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The pure kernel sum over permutations supported on `S` with one orbit on `S`.

This removes the exchange parameter `ζ` from the connected combinatorics so the same object can
later be identified with a cyclic trace expression. -/
noncomputable def singleCycleKernelSum {R : Type*} [CommSemiring R]
    (K : α → α → R) (S : Finset α) : R :=
  ∑ σ : {σ : Equiv.Perm α // σ.support ⊆ S ∧ σ.IsCycleOn (S : Set α)},
    ∏ i : S, K i (σ.1 i)

/-- A connected permutation on `S` carries the common exchange factor `ζ ^ (|S| - 1)`.

This is the coefficient-level W3 boundary: all `ζ` dependence factors out before any cyclic-trace
or formal-power-series argument is introduced. -/
theorem singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum
    {R : Type*} [CommSemiring R] (ζ : R) (K : α → α → R) (S : Finset α) :
    singleCycleContribution ζ K S =
      ζ ^ (S.card - 1) * singleCycleKernelSum K S := by
  classical
  rw [singleCycleContribution, MultiplicativeWeight.connectedContribution]
  change
    (∑ σ : {σ : Equiv.Perm α // σ.support ⊆ S ∧ σ.IsCycleOn (S : Set α)},
      ζ ^ (S.card - 1) * ∏ i : S, K i (σ.1 i)) =
      ζ ^ (S.card - 1) * singleCycleKernelSum K S
  rw [singleCycleKernelSum, Finset.mul_sum]

/-- Fixed-cardinality form of the connected single-cycle kernel theorem. -/
theorem singleCycleContribution_of_card_eq
    {R : Type*} [CommSemiring R] (ζ : R) (K : α → α → R) (S : Finset α)
    (m : ℕ) (hcard : S.card = m) :
    singleCycleContribution ζ K S =
      ζ ^ (m - 1) * singleCycleKernelSum K S := by
  rw [singleCycleContribution_eq_pow_card_mul_singleCycleKernelSum, hcard]

end Combinatorics
