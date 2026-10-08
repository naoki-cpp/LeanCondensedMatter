# Finite-family order decomposition

`Combinatorics.FamilyOrderShuffle` owns the decomposition of a global finite order into local
fiber orders and an order-preserving family shuffle. Its sized API accepts an explicit block-size
function together with a proof that each size is the cardinality of its fiber. The canonical
`Fintype.card` API is a specialization of that seam.

`familyOrdersOfOrder` extracts the fiber-local orders used by the decomposition equivalence.
`familyOrdersOfOrder_strictMono` states that those orders increase in ambient slot number.
The slot-image, increasing-enumeration, and uniqueness implementation remains private to the
family module.

`FinpartitionOrderShuffle` is the semantic adapter for a finite partition. It keeps
`Finset.card` in the partition-facing `PartOrders` and `PartShuffle` types, so downstream
diagrammatic APIs do not acquire cardinality casts. The adapter uses the sized family API with
`F B := ↥(B : Finset α)` and `Fintype.card ↥B = B.card`.
Its `partOrdersOfOrder` uses the same family extraction, and compatibility follows from the
family monotonicity law; the adapter does not construct a second increasing enumeration.

The generic family index may contain empty fibers; those fibers remain zero-size blocks in the
shuffle. A `Finpartition` instead indexes nonempty parts. The adapter retains that invariant and
the partition-facing order and shuffle types while sharing the family extraction implementation.


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

## Component crossing parity and family shuffles

`PerfectPairing.ComponentCrossing` owns the relation between a pairing's residual inter-component
crossing parity and a compatible family shuffle's ordered block-inversion parity.
`Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount` accepts the pair
decomposition, local endpoint equivalences, the shuffle, their endpoint compatibility, and an
explicit block order. It does not assume the residual parity is zero.

The canonical-leg-order and mixed-time-order external-insertion modules supply their own endpoint
data and compatibility proofs. Endpoint inversion reindexing and off-diagonal parity summation
remain in generic combinatorics; time ordering and physical exchange weights remain downstream.

## Removing the first pair

`PerfectPairing.Core` owns the first pair, namely the pair containing position zero.
`PerfectPairing.EraseZero` owns the smaller pairing, its increasing position map, and the residual
pair structure. `eraseZeroPairEmbedding` maps both endpoints back to ambient positions;
`pairs_erase_firstPair_eq_image` identifies all ambient pairs other than the first pair with the
image of the smaller pairing's pairs. Endpoint membership and inverse-coordinate proofs remain
private to that owner.

`PairsDecomposition` derives the product decomposition directly from that structure without
importing crossing geometry. `CrossingEraseZero` uses the same structure together with monotone
crossing transport to derive the crossing-count decomposition. These laws apply also when the
smaller pairing has no pairs.

## Repeated-fiber counting

`Common.FintypeProduct` owns finite-product reindexing and counting.
`Fintype.dvd_sum_equiv_fst_of_dvd_card` derives divisibility of a first-coordinate sum from
divisibility of the repeated fiber's cardinality, using the existing multiplicity formula.
Quartic and TwoPoint crossing-parity proofs supply their own uniform comparisons; the common
counting law handles the four-leg multiplicity and evenness. Vertex-slot geometry and mixed-time
order geometry remain separate downstream responsibilities.
