# Completed-space and infinite-mode boundary

Issue #440 separates four problems that must not be collapsed into one API:

1. completion of the algebraic Fock representation;
2. bounded or unbounded operators and their domains;
3. infinite mode sets and thermal summability;
4. thermodynamic limits.

This roadmap fixes the first completed-space vertical slice and records where each later analytic
obligation belongs.

## Initial representation choice

The first sector is fermionic.  The completed representation itself is defined for an arbitrary
mode type `Mode` by

```lean
SecondQuantization.Fermionic.CompletedFockSpace Mode
  := ℓ²(Fermionic.Occupation Mode, ℂ)
  =  ℓ²(Finset Mode, ℂ).
```

A linear order is introduced only where the existing fermionic sign convention for ladder
operators requires it.  The completion and diagonal thermal constructions do not need a
`LinearOrder Mode` assumption.

The choice is intentionally asymmetric between statistics sectors.

- Every fermionic occupation configuration remains a finite subset of modes, even when `Mode` is
  infinite.
- The existing algebraic Fock space is the finitely supported function space on exactly the same
  configuration type.
- Mathlib's `lp` implementation supplies completeness, an inner product at exponent `2`, canonical
  single-coordinate vectors, and convergence of finite-support truncations.
- Single-mode fermionic occupation is a bounded coordinate projection, so the first operator
  agreement theorem does not require an unbounded-operator interface.

The bosonic completed space is also naturally an `ℓ²` space, but its ladder and number operators are
unbounded.  Starting there would force completion and domain theory to be solved simultaneously,
which is contrary to the issue boundary.

## Completed representation and bounded CAR layer

`Fermionic/CompletedSpace/Basic.lean` provides:

- `CompletedFockSpace Mode`, the `ℓ²` occupation-amplitude Hilbert space;
- `completedBasisState`, the canonical occupation vector;
- `completedOccupationHilbertBasis`, the canonical Hilbert basis on the same occupation index;
- `algebraicToCompleted`, the coordinate-preserving linear inclusion;
- injectivity and dense range of that inclusion;
- `completedNumberOperator`, the bounded projection onto configurations containing one mode;
- agreement of the completed and algebraic number operators on the full algebraic core.

The subsequent toggle/operator/core/CAR files construct bounded completed fermionic creation and
annihilation operators, prove their occupation-basis action and norm bounds, identify them with the
algebraic ladder maps on the dense finite-support core, and lift the canonical anticommutation
relations to the completed Hilbert space.

This validates the representation without pretending that every algebraic operator is bounded.

## Operator boundary

### Bounded continuous operators

An operator belongs in a `ContinuousLinearMap` API only after a norm bound is proved.  The initial
number operator is a coordinate mask and satisfies

```text
‖Nᵢ ψ‖ ≤ ‖ψ‖.
```

The completed fermionic creation and annihilation maps are likewise bounded signed partial
reindexings, so CAR is correctly stated as an identity of bounded operators and connected back to
the existing algebraic theorem on the dense core.

### Unbounded operators

A free Hamiltonian with an unbounded one-particle dispersion and a total number operator over
infinitely many modes are generally unbounded.  They use Mathlib's domain-carrying `LinearPMap`
interface rather than `ContinuousLinearMap`.

`CompletedSpace/Diagonal.lean` defines the maximal weighted `ℓ²` domain for diagonal multiplication,
packages the free Hamiltonian and total number operator on their natural domains, and proves
agreement with the algebraic operators on the finite-support core.  `DiagonalAnalytic.lean` then
proves dense domain, closedness, adjoint identification by conjugating the diagonal weight, and
self-adjointness for real weights.  These analytic results remain separate from the operator
definitions.

Products used in genuinely unbounded Dyson expressions must still state their product domains.  A
formal expression such as `A * exp (-β H)` is not admitted merely because it is meaningful in finite
dimensions.  The completed free-Gibbs pairing recursion does **not** require such an operator product:
its KMS step uses the bounded trace-class pure-point Gibbs density operator together with bounded
ladder operators, and proves cyclic rotation directly from the occupation-basis expectation series.
Thus no additional unbounded `exp (-β H)` product-domain API is part of the completed KMS bridge;
further domain lemmas should be added only when a later unbounded Dyson expression actually consumes
them.

## Thermal-state route

The state-level Gibbs construction is owned by `QuantumTheory.Gibbs.PurePoint`.  The completed free
fermion state specializes that generic construction to

```text
b = completedOccupationHilbertBasis
E = fermionEnergy ε
```

with the explicit state-existence hypothesis

```text
PurePointGibbsSummable (fermionEnergy ε) β.
```

Accordingly, `purePointBoltzmannWeight`, `purePointPartitionFunction`,
`purePointGibbsProbability`, and `purePointGibbsDensityOperator` are the canonical state API.
`CompletedSpace/FreeGibbs.lean` records only the completed occupation-basis action and bounded
expectation-series formulas needed by the fermionic KMS layer.

Unbounded diagonal observables are not passed through the bounded density-state expectation API.
The free Hamiltonian energy uses the generic `QuantumTheory.Gibbs.PurePointExpectation` interface.
For representation-specific diagonal observables, `CompletedSpace/UnboundedExpectation.lean` uses

```text
Summable (fun n => ‖purePointGibbsProbability (fermionEnergy ε) β n * a(n)‖)
```

and defines the corresponding real occupation-series expectation.  This supplies the total-particle
number interface without duplicating the generic pure-point energy expectation.

For free fermions, `CompletedSpace/FreeGibbsSummability.lean` supplies a one-particle sufficient
condition using the same generic summability predicate.  With

```text
qᵢ := purePointBoltzmannWeight ε β i = exp (-β εᵢ),
```

```text
PurePointGibbsSummable ε β
```

implies `PurePointGibbsSummable (fermionEnergy ε) β` because

```text
purePointBoltzmannWeight (fermionEnergy ε) β n = ∏ i ∈ n, qᵢ.
```

The same finite-subset summability theorem yields the infinite product identity

```text
purePointPartitionFunction (fermionEnergy ε) β = ∏' i, (1 + qᵢ).
```

No separate countability typeclass is required by this API: the summability hypothesis itself is
the analytic restriction on the mode family.

The generic `ExpectationPairingRecursion` remains representation independent.  The completed
fermionic implementation packages creation and annihilation as bounded thermal ladders, proves the
Gibbs/KMS rotation against an arbitrary bounded operator, rewrites the CAR peel as an indexed
`List.eraseIdx` sum, and supplies the representation-specific admissibility predicate and first-pair
recurrence.  The common recursion therefore acquires no occupation-basis, countability, or
finite-mode assumptions.

## Finite-mode compatibility and approximation

When `Mode` is finite, `Fermionic.Occupation Mode` is finite and the completed `ℓ²` representation is
finite dimensional. `CompletedSpace/FiniteCompatibility.lean` identifies it canonically and
isometrically with `Common.FiniteHilbertFock (Occupation Mode)` using Mathlib's finite-index
`lpPiLpₗᵢ`.  The equivalence sends completed basis vectors to the finite Hilbert basis and makes the
algebraic-to-completed and algebraic-to-finite Hilbert maps commute. The finite Hilbert realization
and operator transport are owned by `Common/Thermal/FiniteHilbertOperator.lean`, independently of
any thermal state.

`CompletedSpace/FiniteThermalCompatibility.lean` keeps the state-level bridge. Generic pure-point
summability is automatic on the finite occupation index, so both sides use
`finitePurePointGibbsDensityOperator` directly: one on `completedOccupationHilbertBasis`, the other on
`Common.finiteHilbertBasis`. The canonical Hilbert-space isometry intertwines these two
representations because they have the same `purePointGibbsProbability` weights. No separate finite
Gibbs density-state implementation or compatibility module is required.

For arbitrary `Mode`, `CompletedSpace/ModeTruncation.lean` defines the finite-mode coordinate
projections indexed by `Finset Mode`.  They are contractions, fix every algebraic vector once the
finite mode set contains its support, and converge strongly to the identity as a directed net.  No
countability assumption on `Mode` is needed.

`CompletedSpace/GibbsModeTruncation.lean` restricts the generic pure-point free-fermion weights to
the same finite-mode sectors, constructs normalized truncated Gibbs density operators on the full
completed space, and proves convergence of their partition functions and probabilities to the
generic pure-point values under `PurePointGibbsSummable (fermionEnergy ε) β`.
`GibbsModeTruncationExpectation.lean` makes the state topology explicit: for every bounded operator
`A`, the truncated Gibbs expectations converge to the generic pure-point Gibbs expectation on the
completed occupation basis.  This is weak state convergence against bounded observables; no
trace-norm convergence is asserted.

## Staged work

### C1 — completed fermionic core

- [x] Define `ℓ²(Finset Mode, ℂ)` as the completed representation.
- [x] Embed the algebraic Fock space injectively with dense range.
- [x] Extend one bounded operator and prove algebraic-core agreement.

### C2 — bounded CAR operators

- [x] Construct completed creation and annihilation maps as signed partial reindexings.
- [x] Prove norm bounds and basis action.
- [x] Prove agreement on the algebraic core and completed CAR identities.
- [x] Record the completed-space admissibility/KMS implementation for the generic thermal recursion.

### C3 — diagonal unbounded operators

- [x] Define weighted diagonal domains for free Hamiltonians and total number operators.
- [x] Package the operators with a domain-carrying partial-linear-map interface.
- [x] Prove algebraic-core agreement.
- [x] Prove dense-domain, closedness, adjoint, and self-adjointness results separately from the core
  definitions.
- [x] Identify the completed KMS recursion's minimal product-domain boundary: no additional
  unbounded-product lemma is required because the Gibbs state and ladder words are bounded; reserve
  new domain-invariance lemmas for later unbounded Dyson expressions that actually consume them.

### C4 — trace-class free Gibbs state

- [x] Reuse the generic pure-point Gibbs state on the completed occupation basis.
- [x] Prove a useful one-particle sufficient criterion for occupation-level pure-point summability.
- [x] Connect bounded expectations to `DensityOperator.expectation`.
- [x] Keep representation-specific unbounded diagonal expectations separate from the bounded API.
- [x] Prove the free-fermion partition product formula under one-particle summability.

### C5 — compatibility and approximation

- [x] Identify finite-mode completed Fock space with `FiniteHilbertFock`.
- [x] Show the generic finite pure-point Gibbs state commutes with the finite compatibility equivalence.
- [x] Define finite-mode truncations as a `Finset Mode` directed net.
- [x] Prove strong convergence of finite-mode projections and weak convergence of the truncated
  Gibbs states against every bounded observable, with both topologies explicit.

Thermodynamic limits are not part of C1–C5.  They require a separate issue specifying the directed
system, observable algebra, state topology, and uniform estimates.
