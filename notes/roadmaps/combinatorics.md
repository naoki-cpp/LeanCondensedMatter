# Combinatorics roadmap

This roadmap tracks reusable combinatorial infrastructure shared by linked-cluster, diagrammatic,
and finite-index developments.

## Set partitions and cumulants

Status: `proved`.

The project has finite set partitions, Möbius inversion on the partition lattice, cumulants,
connected-class decompositions, and the moment--cumulant bridge needed by linked-cluster arguments.
These live under `Combinatorics` and remain independent of Fock-space or statistics-specific
semantics.

## Pairings and crossing parity

Status: `proved`.

Perfect pairings, endpoint access, crossing predicates/counts, crossing parity, pair decompositions,
and component crossing decompositions live under `Combinatorics/PerfectPairing`. Diagrammatic
layers transport their physical pair data into these general APIs rather than restating crossing
algebra downstream.

## Finite index transformations

Status: `proved`.

`Combinatorics/FiniteIndex` owns statistics-independent finite-index transformations that recur in
operator and diagrammatic proofs, including deletion/reinsertion positions and fixed-width block
coordinates. Downstream layers should expose only the model-specific meaning of an index and reuse
these transformations for arithmetic and ordering facts.

## Exchange signs and permutations

Status: `proved`.

Permutation signs and exchange-sign bookkeeping are factored into general combinatorics before
fermionic or bosonic specializations. This keeps sign algebra separate from operator semantics.

## Finite product decomposition

Status: `proved`.

General finite-product identities and reindexing facts belong upstream of physical amplitudes.
Diagrammatic factorization proofs should reduce to these generic results once the relevant component
or slot equivalence has been constructed.

## Formal-log bridge

Status: `proved`.

`Combinatorics/PowerSeriesCumulant.lean` connects finite-set cumulants to coefficients of a formal
logarithm, including the factorial normalization used by the linked-cluster theorem. The fermionic
Dyson/diagrammatic layer consumes this result rather than reimplementing moment--cumulant algebra.

## Ownership boundary

- set partitions, pairings, cumulants, Möbius inversion, shuffle/reindexing, generic finite product
  identities, and fixed-width finite-index block coordinates/order/counting facts belong in
  `Combinatorics`;
- Mathlib v4.33.1 supplies `finProdFinEquiv : Fin n × Fin k ≃ Fin (n * k)`, finite-product sum
  reindexing, and generic sum divisibility; the cast-aware fixed-width coordinate/order facts and
  block-invariant indicator divisibility used by the project live in
  `Combinatorics/FiniteIndex/Block.lean`; diagrammatic layers specialize this API rather than owning
  separate fixed-leg counting proofs;
- statistics-independent constructions that require Fock/thermal/diagram semantics belong in
  `SecondQuantization.Common`;
- fermionic or bosonic sign/amplitude specializations stay downstream.

## Open work

Add new combinatorial infrastructure only when a downstream theorem exposes a reusable
statistics-independent statement. Higher-point/source-insertion linked-cluster developments should
reuse the existing partition, cumulant, pairing, shuffle, and finite-index APIs rather than create
parallel specialized copies.
