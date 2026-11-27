# Finite-family order decomposition

`Combinatorics.Shuffle.FamilyOrderShuffle` owns the decomposition of a global finite order into local
fiber orders and an order-preserving family shuffle. Its sized API accepts an explicit block-size
function together with a proof that each size is the cardinality of its fiber. The canonical
`Fintype.card` API is a specialization of that seam.

`familyOrdersOfOrder` extracts the fiber-local orders used by the decomposition equivalence.
`familyOrdersOfOrder_strictMono` states that those orders increase in ambient slot number.
The slot-image, increasing-enumeration, and uniqueness implementation remains private to the
family module.

`Shuffle.FinpartitionOrderShuffle` is the semantic adapter for a finite partition. It keeps
`Finset.card` in the partition-facing `PartOrders` and `PartShuffle` types, so downstream
diagrammatic APIs do not acquire cardinality casts. The adapter uses the sized family API with
`F B := ↥(B : Finset α)` and `Fintype.card ↥B = B.card`.
Its `partOrdersOfOrder` uses the same family extraction, and compatibility follows from the
family monotonicity law; the adapter does not construct a second increasing enumeration.

The generic family index may contain empty fibers; those fibers remain zero-size blocks in the
shuffle. A `Finpartition` instead indexes nonempty parts. The adapter retains that invariant and
the partition-facing order and shuffle types while sharing the family extraction implementation.


## Family-shuffle structure, inversion counts, and signs

`FamilySlotShuffle` owns the order-preserving slot equivalence, finite instances, total-size
transport, and empty-family construction. It does not define inversion counts or import modular
arithmetic for those laws.

`Shuffle.FamilySlotShuffleInversions` owns the inter-block inversion counts, their total relative to an
explicit block order, and modular transport. `Shuffle.FamilySlotShuffleSign` derives relative permutation
signs from those counts. Pairing component crossings and external-sector parity use the counts
directly without importing the permutation-sign theorem.

## Binary ambient slots and recursive presentations

`Combinatorics.Shuffle.SlotShuffle` owns order-preserving interleavings of two slot families, their left
and right position sets, complement enumeration, and uniqueness from the left position set.
`slotShuffleLeftSlotSetEquiv` constructs its inverse by increasing enumeration of the left set
and its complement, independently of recursive binary shuffles and their cardinality.
The ambient binomial-cardinality theorem follows from this direct equivalence.

The construction reuses Mathlib's `Finset.orderIsoOfFin` and the generic
`Combinatorics.SetPartition.SubsetSplit` equivalence `subsetSumSdiffEquiv`, which is backed
by `Equiv.Finset.union`. The companion `Combinatorics.SetPartition.SumEquivPartition`
module owns the finite images and subtype reindexing induced by an equivalence of a binary sum.
These two-part decomposition primitives do not depend on the partition lattice or on shuffles;
consumers import their leaves directly. No dependent recursion that removes the first slot is needed.

`Shuffle.BinaryShuffleSlots` owns the adapter from recursive binary shuffles to ambient slot shuffles:
the slot coordinates, monotonicity, injectivity, the equivalence of presentations, and finite-sum
transport. The equivalence uses the independent ambient cardinality result. `Shuffle.FamilySlotShuffleDecomposition` consumes the ambient
module directly. The ordered-simplex product proof still uses recursive binary shuffles internally,
while its integrand is attached to the ambient `SlotShuffle`.

## Component crossing parity and family shuffles

`PerfectPairing.Crossing` owns the crossing-sum reindexing law for strictly monotone endpoint
maps, and the conversion from two oriented crossing sums to a single geometric crossing sum.
Both binary and component decompositions use these laws. `PairEndpoints` owns the product
conversion between a normalized-pair subtype and its underlying finite set. It also constructs normalized-pair
equivalences directly from a single equivalence `A × Fin 2 ≃ α` and partner compatibility;
intermediate coordinate changes are composed at the caller. Endpoint orientation laws are stated
on the induced normalized-pair equivalence itself, rather than on a separate unbundled map.

`PerfectPairing.CrossingParity` owns endpoint-swap invariance and the crossing parity of an
arbitrary ordered normalized-pair presentation. `PerfectPairing.Sign` uses that parity theorem
and owns the consecutive two-slot permutation sign calculation.

`PerfectPairing.CrossingParity` owns the common parity identity for two disjoint families of
normalized pairs, allowing either local endpoint orientation. Binary splitting and component
crossing counts use this same identity to reindex endpoint inversions into position inversions.

`PerfectPairing.ComponentCrossing` owns the relation between a pairing's residual inter-component
crossing parity and a compatible family shuffle's ordered block-inversion parity.
`Pairing.interComponentCrossingCount_mod_two_eq_orderedBlockInversionCount` accepts the pair
decomposition, local endpoint equivalences, the shuffle, their endpoint compatibility, and an
explicit block order. It does not assume the residual parity is zero.

The generic `PairingOn.crossingCount_eq_sum_localCrossingCount_add_inter` additionally
identifies the diagonal contributions with the crossing counts of any order-preserving
component-local pairings, while retaining the exact inter-component remainder.
`PairingOn.crossingCount_mod_two_eq_sum_componentCrossingCount_of_geometric_even`
expresses the common parity consequence of even geometric crossings between distinct
components; Quartic and TwoPoint supply their own four-leg and mixed-time evenness proofs.

The canonical-leg-order and mixed-time-order external-insertion modules supply their own endpoint
data and compatibility proofs. Endpoint inversion reindexing and off-diagonal parity summation
remain in generic combinatorics; time ordering and physical exchange weights remain downstream.

## Binary pairing splits

`PerfectPairing.Restriction` owns restriction along an injective position map with partner-invariant
image, including its partner compatibility and uniqueness. `PerfectPairing.Split` applies these
laws to the two summand injections; assembly and the binary split equivalence remain there.

`PerfectPairing.SplitNormalizedPairs` owns the normalized-pair equivalence, endpoint orientation,
and product factorization for an arbitrary binary position splitting. It does not import crossing
geometry. `PerfectPairing.SplitCrossing` uses that equivalence to decompose crossing counts and
identify the between-sector crossing parity with position-inversion parity. Strict monotonicity
is required only when identifying within-sector counts with local pairing counts.

The within-sector crossing sums use `sum_sum_crosses_eq_of_equiv` from `PerfectPairing.Crossing`.
The binary parity laws allow endpoint reversals; the compatible-endpoint hypotheses of family
component crossings do not replace those laws directly.

## Component-pair embeddings

The quartic diagram data module imports only `PerfectPairing.Core`; the two-point diagram data
module imports `PerfectPairing.VertexGraph`. Thermal pairing weights import the split-crossing,
first-pair crossing, and the pairing core for scalar evaluation. The full `PerfectPairing` umbrella remains
an aggregate entry point rather than a dependency of these foundational consumers.

`PerfectPairing.Core` owns normalized pairs of `PairingOn` on finite linear orders, including
membership preservation and reflection under partner-intertwining order embeddings. `PerfectPairing.Embedding` owns normalized-pair embeddings between finite linear orders induced by partner-intertwining order
embeddings, including preservation and reflection of crossings. Quartic fixed-order component pairs
use that construction with the canonical component-local vertex orders and component shuffle.
The equality of the assembled vertex order with the fixed order supplies the partner compatibility;
component assignment remains in the Quartic adapter.

The component decomposition uses arbitrary finite linearly ordered position fibers. Binary splitting
and its inverse laws use arbitrary sum equivalences, without finiteness or order assumptions; only
the normalized-pair and crossing-count layers require finite linear orders. The ordered block-shuffle
and permutation-sign statements retain their explicit finite-index coordinates.

## Removing the first pair

`PerfectPairing.Core` owns the pairing bundle, disjoint-sum assembly and transport along
arbitrary position equivalences, as well as the first pair containing position zero.
`PerfectPairing.FirstPair` owns the smaller pairing, its increasing position map, and the residual
pair structure. `eraseZeroPairEmbedding` maps both endpoints back to ambient positions;
`pairs_erase_firstPair_eq_image` identifies all ambient pairs other than the first pair with the
image of the smaller pairing's pairs. Its membership proofs reuse the core order-embedding law
and endpoint separation from `PerfectPairing.PairEndpoints`. Inverse-coordinate proofs remain
private to that owner.

`FiniteIndex.DeletedPositions` also supplies the sum equivalence separating the two removed
positions from the remaining ordered positions. `PerfectPairing.FirstPair` transports
the disjoint sum of a two-element pairing and the smaller pairing along that equivalence.
It owns both the product decomposition of the normalized
pair set and the additive reindexing of sums through `Pairing.equivSigma`. These structural laws
do not depend on crossing geometry, and the product law also applies when the smaller pairing has
no pairs. `CrossingEraseZero` uses the residual structure and monotone crossing transport to
derive the crossing-count decomposition.

## List deletion and indexed sums

`FiniteIndex.EraseIdxOfFn` owns the deletion coordinate law for `List.ofFn` and the finite-sum
reindexing law `List.sum_getElem_eraseIdx_ofFn`. The latter transports a summand depending on the
entry index, selected entry, and remaining list to the original finite coordinates. Common finite
Gibbs, Bosonic free Gibbs, and completed Fermionic Gibbs pairing recursions use this law;
summability, KMS rotation, and trace hypotheses remain with their respective thermal realizations.

## Repeated-fiber counting

`Common.FintypeProduct` owns finite-product reindexing and counting.
`Fintype.dvd_sum_equiv_fst_of_dvd_card` derives divisibility of a first-coordinate sum from
divisibility of the repeated fiber's cardinality, using the existing multiplicity formula.
`PerfectPairing.ComponentCrossing` combines this counting law with the generic endpoint-inversion
formula: constant comparison order over an even-sized fiber makes cross-component geometric
crossing parity vanish. Quartic and TwoPoint supply their own fiber coordinates and uniform-order
proofs; vertex-slot geometry and mixed-time order geometry remain separate downstream.

## Partition products and moment transforms

`Combinatorics.SetPartition.FinpartitionProduct` owns `Finpartition.partitionProduct` and its top-partition
and `bind` laws over a commutative monoid. It does not depend on the moment transform or
Möbius inversion.

`Cumulant.Moment` owns sums over partitions and therefore requires a commutative semiring.
Its distinguished-block product law is the adapter to the distinguished-block decomposition.
`Cumulant.Inversion` adds the Möbius inverse over a commutative ring. Restriction and
independence-specific product laws remain in `Cumulant.Independence`.
