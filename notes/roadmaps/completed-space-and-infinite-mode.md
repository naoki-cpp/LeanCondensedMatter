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

Products used in KMS or Dyson expressions must still state their product domains.  A formal
expression such as `A * exp (-β H)` is not admitted merely because it is meaningful in finite
dimensions.

## Thermal-state route

`CompletedSpace/FreeGibbs.lean` constructs the free completed Gibbs state from the minimal explicit
occupation-level hypothesis

```text
Summable (fun n : Occupation Mode => ‖exp (-β E(n))‖).
```

The hypothesis gives a positive finite partition sum and a normalized diagonal trace-class
`QuantumTheory.DensityOperator`.  Bounded observables therefore use the canonical
`DensityOperator.expectation` from #421, with an explicit occupation-basis `tsum` formula.

Unbounded diagonal observables are not passed through that bounded API.
`CompletedSpace/UnboundedExpectation.lean` instead uses the separate condition

```text
Summable (fun n => ‖pβ(n) * a(n)‖)
```

and defines the corresponding real occupation-series expectation, including specializations to the
free Hamiltonian energy and total particle number.

For free fermions, `CompletedSpace/FreeGibbsSummability.lean` supplies a more practical one-particle
sufficient condition.  With

```text
qᵢ := exp (-β εᵢ),
```

`Summable q` implies the occupation-level Gibbs summability because

```text
exp (-β E(n)) = ∏ i ∈ n, qᵢ.
```

The same finite-subset summability theorem yields the infinite product identity

```text
Z(β) = ∏' i, (1 + qᵢ).
```

No separate countability typeclass is required by this API: the summability hypothesis itself is
the analytic restriction on the mode family.

The generic `ExpectationPairingRecursion` from #421 remains representation independent.  A completed
fermionic or bosonic instance must supply its own admissibility predicate, KMS laws, and product-domain
conditions; the recursion itself should not acquire occupation-basis or finiteness assumptions.

## Finite-mode compatibility and approximation

When `Mode` is finite, `Fermionic.Occupation Mode` is finite and the completed `ℓ²` representation is
finite dimensional. `CompletedSpace/FiniteCompatibility.lean` identifies it canonically and
isometrically with `Common.FiniteHilbertFock (Occupation Mode)` using Mathlib's finite-index
`lpPiLpₗᵢ`.  The equivalence preserves every occupation coordinate, sends completed basis vectors to
the existing finite Hilbert basis, and makes the algebraic-to-completed and algebraic-to-finite
Hilbert maps commute.

`CompletedSpace/FiniteOperatorCompatibility.lean` lifts algebraic-core agreement through this
isometry: any bounded completed operator that agrees with an algebraic Fock endomorphism transports
to the existing `Common.finiteHilbertOperator`.  In particular the completed number, creation, and
annihilation operators coincide with their finite-Hilbert realizations.

`CompletedSpace/FiniteThermalCompatibility.lean` identifies the thermal data.  Finite mode sets make
the completed Gibbs summability condition automatic; the completed and finite Boltzmann weights,
partition functions, and normalized probabilities agree; and the completed free Gibbs density
operator intertwines with the existing finite Gibbs density operator under the same isometry.

For arbitrary `Mode`, `CompletedSpace/ModeTruncation.lean` defines the finite-mode coordinate
projections indexed by `Finset Mode`.  They are contractions, fix every algebraic vector once the
finite mode set contains its support, and converge strongly to the identity as a directed net.  No
countability assumption on `Mode` is needed.

`CompletedSpace/GibbsModeTruncation.lean` restricts the free Boltzmann weights to the same finite-mode
sectors, constructs normalized truncated Gibbs density operators on the full completed space, and
proves convergence of the truncated partition functions and occupation probabilities under the
existing absolute Gibbs summability assumption.  `GibbsModeTruncationExpectation.lean` makes the
state topology explicit: for every bounded operator `A`, the truncated Gibbs expectations converge
to the full completed Gibbs expectation.  This is weak state convergence against bounded
observables; no trace-norm convergence is asserted.

## Staged work

### C1 — completed fermionic core

- [x] Define `ℓ²(Finset Mode, ℂ)` as the completed representation.
- [x] Embed the algebraic Fock space injectively with dense range.
- [x] Extend one bounded operator and prove algebraic-core agreement.

### C2 — bounded CAR operators

- [x] Construct completed creation and annihilation maps as signed partial reindexings.
- [x] Prove norm bounds and basis action.
- [x] Prove agreement on the algebraic core and completed CAR identities.
- [ ] Record a completed-space admissibility/KMS instance for generic thermal recursion when its
  product-domain requirements are available.

### C3 — diagonal unbounded operators

- [x] Define weighted diagonal domains for free Hamiltonians and total number operators.
- [x] Package the operators with a domain-carrying partial-linear-map interface.
- [x] Prove algebraic-core agreement.
- [x] Prove dense-domain, closedness, adjoint, and self-adjointness results separately from the core
  definitions.
- [ ] Add product-domain/domain-invariance lemmas required by later KMS or unbounded Dyson products.

### C4 — trace-class free Gibbs state

- [x] State explicit occupation-level Boltzmann summability and a useful mode-level sufficient
  criterion.
- [x] Construct the diagonal trace-class Gibbs state with positive normalization.
- [x] Connect bounded expectations to `DensityOperator.expectation`.
- [x] Provide a separate integrability and expectation interface for unbounded diagonal observables.
- [x] Prove the free-fermion partition product formula under mode-level summability.

### C5 — compatibility and approximation

- [x] Identify finite-mode completed Fock space with `FiniteHilbertFock`.
- [x] Show finite Gibbs density/operator APIs commute with the finite compatibility equivalence.
- [x] Define finite-mode truncations as a `Finset Mode` directed net.
- [x] Prove strong convergence of finite-mode projections and weak convergence of the truncated
  Gibbs states against every bounded observable, with both topologies explicit.

Thermodynamic limits are not part of C1–C5.  They require a separate issue specifying the directed
system, observable algebra, state topology, and uniform estimates.
