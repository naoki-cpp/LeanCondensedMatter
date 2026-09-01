# Completed-space and infinite-mode boundary

Completion, unbounded-operator domains, thermal summability, and thermodynamic limits are separate
analytic problems. This note records the current fermionic completed-space boundary and what remains
open.

## Completed fermionic representation

```lean
SecondQuantization.Fermionic.CompletedFockSpace Mode
  := ℓ²(Fermionic.Occupation Mode, ℂ)
```

`SecondQuantization.Fermionic.CompletedSpace` owns:

- the canonical occupation Hilbert basis and dense algebraic core;
- bounded completed number, creation, and annihilation operators;
- agreement with the algebraic operators on the finite-support core;
- completed CAR identities;
- maximal diagonal `LinearPMap` operators for unbounded one-particle weights;
- dense-domain, closedness, adjoint, and self-adjointness results for real diagonal weights;
- explicit product domains and free-Hamiltonian/ladder relations;
- finite-dimensional compatibility and finite-mode coordinate truncations.

Bounded operators use `ContinuousLinearMap`; genuinely unbounded diagonal operators keep explicit
`LinearPMap` domains. Completion alone never licenses coercing an unbounded Hamiltonian or number
operator to a bounded map.

## Thermal boundary

Completed thermal specializations live under `SecondQuantization.Fermionic.Thermal.Completed`, while
the state-level pure-point Gibbs construction is owned by `QuantumTheory.Gibbs.PurePoint`.

The completed free-fermion route includes:

- pure-point Gibbs states under explicit `PurePointGibbsSummable` hypotheses;
- occupation-basis expectation formulas and unbounded diagonal expectations on explicit summability
  domains;
- a one-particle sufficient condition for free-fermion Gibbs summability and the corresponding
  partition-product identity;
- bounded thermal ladder packaging, Gibbs intertwining, KMS rotation, CAR peel, and the completed
  Bloch--de Dominicis recursion;
- finite-mode Gibbs truncations and convergence of bounded-observable expectations to the completed
  pure-point Gibbs expectation.

The last item is weak convergence against bounded observables, not a thermodynamic limit or a general
trace-norm convergence theorem.

## Finite-mode compatibility

For finite `Mode`, the completed occupation space is finite dimensional and is canonically related to
the finite Hilbert Fock realization through `SecondQuantization.Common.CompletedSpace` compatibility
results. The same generic pure-point Gibbs probabilities are used on both representations; no
independent finite Gibbs state model is required.

For arbitrary `Mode`, finite-mode projections indexed by `Finset Mode` are contractions, eventually
fix algebraic vectors, and converge strongly to the identity. No countability assumption on `Mode` is
needed for that representation-level statement.

## Open work

- completed bosonic Fock-space operator theory, where ladder and number operators are unbounded;
- interacting completed-space Dyson theory with all required product domains;
- stronger convergence topologies for Gibbs truncations when justified;
- infinite-volume or thermodynamic limits with an explicit directed system, observable algebra,
  state topology, and uniform estimates.
