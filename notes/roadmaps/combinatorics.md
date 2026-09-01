# Combinatorics (Track B)

Track B contains physics-independent finite combinatorics used by the thermal and diagrammatic layers.

## Partition-lattice Möbius theory

Status: `proved`.

`Combinatorics/PartitionLattice.lean` and the set-partition modules provide the refinement structure
needed for incidence-algebra arguments. The key results include:

- refinement intervals represented as products of partition lattices on the blocks;
- the corresponding order isomorphism;
- factorization of the Möbius function over blocks;
- the explicit partition-lattice formula

```text
μ(⊥, ⊤) = (-1)^(n-1) (n-1)!
```

for a nonempty `n`-element set, together with interval/blockwise versions.

General incidence-algebra support such as invariance under order isomorphism, down-set compatibility,
and finite dependent-product factorization lives in `Combinatorics/IncidenceAlgebraMu.lean`.

## Moment--cumulant inversion

Status: `proved` in `Combinatorics/MomentCumulant.lean`.

For a finite set `S`,

```text
momentFromCumulant κ S
  = ∑ π : Finpartition S, ∏ B ∈ π.parts, κ B,
```

and

```text
cumulantFromMoment m S
  = ∑ π : Finpartition S, μ(π, ⊤) ∏ B ∈ π.parts, m B.
```

The two constructions are mutual inverses on nonempty sets. The nonempty hypothesis is genuine:
`momentFromCumulant κ ∅ = 1` independently of `κ ∅`.

The proof uses the refinement-product decomposition to factor partition products and applies Möbius
inversion on the partition lattice.

## Cumulants and independence

Status: `proved` in `Combinatorics/CumulantFactorization.lean`.

`Finpartition.IsIndependentAcross` expresses factorization of a moment function across two disjoint
regions. Under that hypothesis, cumulants vanish on finite sets that straddle both regions; in
particular the cumulant of their nontrivial union is zero.

This is the reusable finite combinatorial independence theorem. Physics-specific notions of state or
operator independence belong downstream.

## Formal-log bridge

Status: `proved`.

`Combinatorics/PowerSeriesCumulant.lean` connects finite-set cumulants to coefficients of a formal
logarithm, including the factorial normalization used by the linked-cluster theorem. The fermionic
Dyson/diagrammatic layer consumes this result rather than reimplementing moment--cumulant algebra.

## Ownership boundary

- set partitions, pairings, cumulants, Möbius inversion, shuffle/reindexing, and generic finite
  product identities belong in `Combinatorics`;
- statistics-independent constructions that require Fock/thermal/diagram semantics belong in
  `SecondQuantization.Common`;
- fermionic or bosonic sign/amplitude specializations stay downstream.

## Open work

Add new combinatorial infrastructure only when a downstream theorem exposes a reusable
statistics-independent statement. Higher-point/source-insertion linked-cluster developments should
reuse the existing partition, cumulant, pairing, and shuffle APIs rather than create parallel
specialized copies.
