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
