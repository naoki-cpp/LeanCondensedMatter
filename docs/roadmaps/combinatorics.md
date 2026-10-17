# Combinatorics (Track B)

Track B contains physics-independent finite combinatorics used by the thermal and diagrammatic layers.

## Partition-lattice Möbius theory

Status: `proved`.

The set-partition infrastructure is split by responsibility:

- `Combinatorics/SetPartition/Refinement.lean` and
  `Combinatorics/SetPartition/Coarsening.lean` provide the order-theoretic decomposition of
  refinement and coarsening intervals;
- `Combinatorics/SetPartition/Mobius.lean` proves Möbius invariance/factorization results for those
  intervals;
- `Combinatorics/SetPartition/MobiusFormula.lean` proves the explicit partition-lattice formula

```text
μ(⊥, ⊤) = (-1)^(n-1) (n-1)!
```

for a nonempty `n`-element set, together with the top-interval and blockwise interval formulas.

General incidence-algebra support such as invariance under order isomorphism, down-set/up-set
compatibility, and finite dependent-product factorization lives in
`Combinatorics/IncidenceAlgebra/Mobius.lean`.

The explicit factorial formula is proved entirely within finite combinatorics. The proof combines
the finite cumulant-inversion API with the distinguished-block decomposition of set partitions, so
the set-partition layer does not depend on `Analysis.PowerSeries.Cumulant`.

## Moment--cumulant inversion

Status: `proved`.

`Combinatorics/Cumulant/Moment.lean` defines the finite-set moment transform over a commutative
semiring:

```text
momentFromCumulant κ S
  = ∑ π : Finpartition S, ∏ B ∈ π.parts, κ B.
```

`Combinatorics/Cumulant/Inversion.lean` defines the Möbius-inverse cumulant transform over a
commutative ring:

```text
cumulantFromMoment m S
  = ∑ π : Finpartition S, μ(π, ⊤) ∏ B ∈ π.parts, m B.
```

The two constructions are mutual inverses on nonempty sets. The nonempty hypothesis is genuine:
`momentFromCumulant κ ∅ = 1` independently of `κ ∅`. The normalized bundled API that removes this
pointwise side condition lives in `Combinatorics/Cumulant/Normalized.lean`.

The proof uses the refinement-product decomposition to factor partition products and applies Möbius
inversion on the partition lattice.

## Cumulants and independence

Status: `proved`.

`Combinatorics/Cumulant/Independence.lean` contains the reusable finite combinatorial independence
theorems. Under factorization of moments across two disjoint regions, cumulants vanish on finite
sets that straddle both regions; in particular the cumulant of their nontrivial union is zero.

Physics-specific notions of state or operator independence belong downstream.

## Connected decompositions

Status: `proved`.

`Combinatorics/Cumulant/ConnectedDecomposition.lean` and
`Combinatorics/Cumulant/ConnectedDecompositionInversion.lean` package multiplicative
connected-component decompositions and identify their connected contributions with finite-set
cumulants. These are the combinatorial APIs consumed by linked-cluster developments.

## Formal-log bridge

Status: `proved`.

The formal-power-series bridge is owned by `Analysis/PowerSeries/Cumulant.lean`, not by the finite
combinatorics layer. It connects factorial-normalized coefficients of a formal logarithm with the
finite-set cumulant API and provides the connected-contribution theorem used downstream by the
linked-cluster development.

Generic power-series logarithm algebra remains in `Analysis/PowerSeries`; finite partitions,
cumulants, and connected decompositions remain in `Combinatorics`.

## Fixed-width blocks and Stirling enumeration

Mathlib supplies `finProdFinEquiv` for the underlying finite-index bijection. The
project's `FiniteIndex/Block.lean` keeps its equality-cast-aware coordinate reconstruction,
lexicographic order characterization `blockEquiv_lt_iff`, and the order-preserving
`blockMap` interface: these are not supplied by the underlying equivalence alone.
The internal arithmetic lemmas stay private; downstream pairing and diagrammatic code
uses the public coordinate/order facts.

Mathlib's `Nat.stirlingSecond` and `Nat.stirlingSecond_succ_succ` supply the
number and its recurrence, but do not directly count the subtype of `Finpartition s`
with exactly `k` blocks. `SetPartition/Stirling.lean` proves
`Finpartition.card_parts_eq_stirlingSecond` using distinguished-block decomposition.
The binomial-convolution and reflected-index identities remain private proof lemmas.
`Finpartition.card_coarsenings_parts_eq_stirlingSecond` is a separate transport of
this count through `coarseningsEquivBlockPartitions`; neither public counting theorem
is only a wrapper around Mathlib's recurrence.

## Ownership boundary

- finite-set off-diagonal sum congruences modulo `n` belong in
  `Combinatorics/FiniteSumModEq.lean`; pairing-crossing proofs consume that general result without
  owning it;
- set partitions, pairings, cumulants, Möbius inversion, shuffle/reindexing, generic finite product
  identities, and fixed-width finite-index block coordinates/order facts belong in `Combinatorics`;
- `Combinatorics/SetPartition/SubsetSplit.lean` and
  `Combinatorics/SetPartition/SumEquivPartition.lean` own reusable two-part decompositions:
  a finite subset and its relative complement, or the two images of a sum equivalence.
  These primitives are independent of the partition lattice and are imported directly by
  shuffle, pairing, and diagrammatic consumers;
- `Combinatorics/Shuffle/` owns order-preserving binary and finite-family shuffles, their signs,
  inversion counts, recursive decompositions, and finite-partition order adapters;
- Mathlib provides `SimpleGraph.reachableSetoid`, connected components, and
  `Finpartition.ofSetoid` / `Finpartition.ofSetSetoid`, but no graph-component `Finpartition`
  facade was found. The finite and ambient-finset graph component API therefore lives in
  `Combinatorics/SetPartition/GraphComponents.lean`; diagrammatic layers keep only semantic
  component definitions and consume these generic graph lemmas directly;
- Mathlib supplies `finProdFinEquiv : Fin n × Fin k ≃ Fin (n * k)` and finite-product sum
  reindexing; the cast-aware fixed-width coordinate/order facts used by the project live in
  `Combinatorics/FiniteIndex/Block.lean`, while generic counting through an equivalence with a
  finite product lives in `Combinatorics/Common/FintypeProduct.lean`;
- duplicate-free flattened-list block order belongs in
  `Combinatorics/Common/ListFlatMapOrder.lean`, independently of its imaginary-time consumer;
- signs of fiberwise permutations on dependent sums belong in
  `Permutation/SigmaPermutationSign.lean`, under `Equiv.Perm`, independently of the
  diagrammatic relative-shuffle consumer;
- generic formal power-series algebra and the formal-log/cumulant bridge live in
  `Analysis/PowerSeries`; pure set-partition theorems should not acquire new power-series
  dependencies;
- statistics-independent constructions that require Fock/thermal/diagram semantics belong in
  `SecondQuantization.Common`;
- fermionic or bosonic sign/amplitude specializations stay downstream.

## Open work

- Add new combinatorial infrastructure only when a downstream theorem exposes a reusable
  statistics-independent statement.
- Higher-point/source-insertion linked-cluster developments should reuse the existing partition,
  cumulant, pairing, shuffle, and finite-index APIs rather than create parallel specialized copies.
