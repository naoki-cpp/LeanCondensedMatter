# Completed-space and infinite-mode boundary

Issue #440 separates four problems that must not be collapsed into one API:

1. completion of the algebraic Fock representation;
2. bounded or unbounded operators and their domains;
3. infinite mode sets and thermal summability;
4. thermodynamic limits.

This roadmap fixes the first completed-space vertical slice and records where each later analytic
obligation belongs.

## Initial representation choice

The first sector is fermionic.  For an arbitrary linearly ordered mode type `Mode`, use

```lean
SecondQuantization.Fermionic.CompletedFockSpace Mode
  := ℓ²(Fermionic.Occupation Mode, ℂ)
  =  ℓ²(Finset Mode, ℂ).
```

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

## Implemented first slice

`Fermionic/CompletedSpace/Basic.lean` provides:

- `CompletedFockSpace Mode`, the `ℓ²` occupation-amplitude Hilbert space;
- `completedBasisState`, the canonical occupation vector;
- `algebraicToCompleted`, the coordinate-preserving linear inclusion;
- injectivity and dense range of that inclusion;
- `completedNumberOperator`, the bounded projection onto configurations containing one mode;
- agreement of the completed and algebraic number operators on the full algebraic core.

This validates the representation without pretending that every algebraic operator is bounded.

## Operator boundary

### Bounded continuous operators

An operator belongs in a `ContinuousLinearMap` API only after a norm bound is proved.  The initial
number operator is a coordinate mask and satisfies

```text
‖Nᵢ ψ‖ ≤ ‖ψ‖.
```

Fermionic creation and annihilation operators are expected to extend boundedly, but their completed
versions should be introduced only after the signed partial reindexing is constructed and its norm
bound is proved.  CAR should then be stated as an identity of bounded operators and connected back to
the existing algebraic theorem on the dense core.

### Unbounded operators

A free Hamiltonian with an unbounded one-particle dispersion and a total number operator over
infinitely many modes are generally unbounded.  They must use a domain-carrying interface such as
Mathlib's `LinearPMap`, or a later closed/self-adjoint specialization, rather than
`ContinuousLinearMap`.

The first domain should be an explicit weighted square-summability condition on occupation
amplitudes.  Agreement with the algebraic operator is a core theorem; essential self-adjointness or
closure is a later result, not part of the definition.

Products used in KMS or Dyson expressions must state their product domains.  A formal expression
such as `A * exp (-β H)` is not admitted merely because it is meaningful in finite dimensions.

## Thermal-state route

The completed representation alone does not produce a Gibbs state.  A later slice should assume:

- a countable configuration basis or an equivalent spectral enumeration;
- a real occupation energy `E` bounded below;
- explicit summability of `exp (-β E n)`;
- positivity and nonzero normalization of the partition sum.

Under those hypotheses, the diagonal Gibbs operator can be shown trace class and normalized into the
existing `QuantumTheory.DensityOperator`.  Bounded observables then use the canonical
`DensityOperator.expectation` from #421.  Expectations of unbounded observables need a separate
integrability/domain statement and must not be routed through the bounded-observable API.

The generic `ExpectationPairingRecursion` from #421 remains representation independent.  A completed
fermionic or bosonic instance must supply its own admissibility predicate, KMS laws, and product-domain
conditions; the recursion itself should not acquire occupation-basis or finiteness assumptions.

## Finite-mode compatibility

When `Mode` is finite, `Fermionic.Occupation Mode` is finite and the completed `ℓ²` representation is
finite dimensional.  A later compatibility theorem should identify it isometrically with the current
`Common.FiniteHilbertFock` realization and show that the density-state, finite trace, and completed
number-operator APIs commute with that identification.

This compatibility theorem is distinct from the algebraic-to-completed inclusion: the former relates
two Hilbert realizations under finite hypotheses, while the latter embeds the finite-support core for
any mode type.

## Staged work

### C1 — completed fermionic core

- [x] Define `ℓ²(Finset Mode, ℂ)` as the completed representation.
- [x] Embed the algebraic Fock space injectively with dense range.
- [x] Extend one bounded operator and prove algebraic-core agreement.

### C2 — bounded CAR operators

- [ ] Construct completed creation and annihilation maps as signed partial reindexings.
- [ ] Prove norm bounds and basis action.
- [ ] Prove agreement on the algebraic core and completed CAR identities.
- [ ] Record the resulting bounded-operator admissibility for generic thermal recursion.

### C3 — diagonal unbounded operators

- [ ] Define weighted diagonal domains for free Hamiltonians and total number operators.
- [ ] Package the operators with a partial-linear-map or closed-operator interface.
- [ ] Prove algebraic-core agreement and basic domain invariance.
- [ ] Separate core identities from closure and self-adjointness theorems.

### C4 — trace-class free Gibbs state

- [ ] State countability and Boltzmann-weight summability hypotheses.
- [ ] Construct the diagonal trace-class Gibbs state.
- [ ] Connect bounded expectations to `DensityOperator.expectation`.
- [ ] State the separate integrability interface for unbounded observables.

### C5 — compatibility and approximation

- [ ] Identify finite-mode completed Fock space with `FiniteHilbertFock`.
- [ ] Define finite-mode or finite-energy truncations.
- [ ] Prove the first strong or norm convergence statements with topology explicit.

Thermodynamic limits are not part of C1–C5.  They require a separate issue specifying the directed
system, observable algebra, state topology, and uniform estimates.
