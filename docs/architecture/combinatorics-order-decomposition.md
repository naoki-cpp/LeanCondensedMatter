# Finite-family order decomposition

`Combinatorics.FamilyOrderShuffle` owns the decomposition of a global finite order into local
fiber orders and an order-preserving family shuffle. Its sized API accepts an explicit block-size
function together with a proof that each size is the cardinality of its fiber. The canonical
`Fintype.card` API is a specialization of that seam.

`FinpartitionOrderShuffle` is the semantic adapter for a finite partition. It keeps
`Finset.card` in the partition-facing `PartOrders` and `PartShuffle` types, so downstream
diagrammatic APIs do not acquire cardinality casts. The adapter uses the sized family API with
`F B := ↥(B : Finset α)` and `Fintype.card ↥B = B.card`.

The generic family index may contain empty fibers; those fibers remain zero-size blocks in the
shuffle. A `Finpartition` instead indexes nonempty parts, and its existing part-slot utilities
continue to express that invariant. The adapter must not replace those partition-specific
utilities with generic names merely to reduce line count.


## Binary ambient slots and recursive presentations

`Combinatorics.SlotShuffle` owns order-preserving interleavings of two slot families, their left
and right position sets, complement enumeration, and uniqueness from the left position set.
`slotShuffleLeftSlotSetEquiv` constructs its inverse by increasing enumeration of the left set
and its complement, independently of recursive binary shuffles and their cardinality.
The ambient binomial-cardinality theorem follows from this direct equivalence.

The construction reuses Mathlib's `Finset.orderIsoOfFin` and `subsetSumSdiffEquiv`, which is backed
by `Equiv.Set.sumDiffSubset`. No dependent recursion that removes the first slot is needed.

`BinaryShuffleSlots` maps the recursive presentation to ambient positions.
`BinaryShuffleSlotEquiv` owns injectivity and the equivalence with that recursive presentation;
it uses the ambient cardinality result. `FamilySlotShuffleDecomposition` consumes the ambient
module directly. The ordered-simplex product proof still uses recursive binary shuffles internally,
while its integrand is attached to the ambient `SlotShuffle`.
