# Finite combinatorics context

## Slot orderings

**Ambient slot shuffle**:
An interleaving of two finite ordered families of positions that preserves the order within each
family. It is uniquely determined by the set of positions occupied by the left family.
_Avoid_: arbitrary permutation, recursive presentation

**Fiber-local order**:
The elements of one fiber listed in the order of their positions in a global finite order.
Empty fibers retain their unique empty order.
_Avoid_: arbitrary fiber enumeration

## Pairings and crossings

**Perfect pairing**:
A fixed-point-free involutive permutation (`PairingOn α`), with no finiteness or order
required by the bundle itself. `Pairing n` is its specialization to `Fin (2 * n)`.
_Avoid_: an inherently ordered or finite matching structure

**Normalized pair**:
On a finite linear order, the representative `(a, b)` with `a < b` of a partner orbit.
The set of normalized pairs enumerates each orbit once.
_Avoid_: an extra independent choice of pair orientation

**Geometric crossing count**:
The number of interleaving pairs of distinct normalized pairs. The oriented test
`Crosses (a,b) (c,d)` means `a < c < b < d`; counting this test over ordered pairs of
normalized pairs counts each geometric crossing once. The count depends on the ambient
linear order, whereas the underlying pairing does not.
_Avoid_: a permutation-invariant property under arbitrary endpoint relabeling

Implementation: [`PerfectPairing.Core`](../../../LeanCondensedMatter/Combinatorics/PerfectPairing/Core.lean)
and [`PerfectPairing.Crossing`](../../../LeanCondensedMatter/Combinatorics/PerfectPairing/Crossing.lean).
