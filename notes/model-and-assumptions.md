# Models and assumptions

This document records the physical models used by the project and the assumptions represented by
the current Lean APIs. Module ownership is described in the track roadmaps and architecture notes.

## Quantum-mechanical foundation

### Pure states and observables

- A pure state is represented by a unit vector `QuantumTheory.State H` in a complex Hilbert space.
- An observable is a bounded self-adjoint operator `QuantumTheory.Observable H`.
- `QuantumTheory.expValue` is the vector-state expectation value.
- Global phase invariance of expectation values is proved, but physical states are not yet quotiented
  by phase.

### Mixed states

`QuantumTheory.DensityOperator H` is the only mixed-state representation. Its underlying bounded
operator is positive, compact, self-adjoint, spectrally trace-class, and normalized to spectral
trace `1`.

The model is dimension-independent. In finite dimensions, specialization theorems recover ordinary
matrix trace formulas without changing the state type.

`QuantumTheory.pure` embeds a unit vector as the rank-one projector `|ψ⟩⟨ψ|`. This is not
purification of a mixed state on an enlarged Hilbert space.

### Measurements

`QuantumTheory.POVM H M` represents a discrete measurement with a countable outcome type. Its
positive effects sum strongly to the identity. `QuantumTheory.prob` is the real Born probability
obtained from the density-state expectation of an effect.

The current measurement model does not include continuous outcomes or operator-valued measures on
measurable spaces.

### Entropy

`QuantumTheory.vonNeumannEntropy` is the eigenvalue sum of `-λ log λ` with codomain `ENNReal`.
Infinite entropy is represented by `⊤`. In finite dimensions the entropy is proved finite and its
real value is obtained through `.toReal`.

Boltzmann’s principle, identifying `k_B` times von Neumann entropy with thermodynamic entropy, is a
physical postulate and is not formalized as an equality in this project.

## Gibbs states and equilibrium

For a bounded Hamiltonian `Hop`, the project defines

```text
gibbsOp Hop β = exp (-β Hop)
```

through continuous functional calculus. A normalized `gibbsState` is constructed from explicit
compactness, spectral-summability, and nonzero-trace hypotheses.

For Hamiltonians represented instead by pure-point spectral data, `QuantumTheory.Gibbs.PurePoint`
constructs the density state directly from a Hilbert basis and real energies. Its canonical API is

```text
purePointBoltzmannWeight
purePointPartitionFunction
purePointGibbsProbability
purePointGibbsDensityOperator
```

with `PurePointGibbsSummable` as the explicit state-existence hypothesis. On a finite spectral index,
`finitePurePointGibbsDensityOperator` is the direct specialization and requires no independent finite
Gibbs-state implementation.

The Helmholtz free-energy theorem proves the Gibbs lower bound under its stated hypotheses, and the
bounded-Hamiltonian Gibbs state satisfies the corresponding entropy identity. For `β > 0`, equality
in the Helmholtz bound holds exactly for the canonical Gibbs state under the same compactness,
summability, and nonzero-trace hypotheses.

A bounded Hamiltonian cannot model a genuinely infinite-dimensional compact Gibbs operator: the
operator exponential is invertible, so compactness forces finite dimensionality. Infinite-volume or
infinite-mode Gibbs theory therefore requires an unbounded self-adjoint Hamiltonian or a semigroup
interface with domain control; pure-point spectral data provide one state-level route when the
Boltzmann weights are summable.

## Finite-temperature linked-cluster theory

### Physical target

The linked-cluster theorem states that the perturbative expansion of `log Z` contains only connected
contributions. The project separates three levels:

1. a combinatorial moment–cumulant theory over finite set partitions;
2. formal or coefficientwise perturbative identities;
3. analytic finite-dimensional partition-function identities near zero coupling.

The formal/combinatorial core does not assert convergence of an infinite-volume perturbation series
or existence of a thermodynamic limit.

### Hilbert-space scope

The long-term physical model is a countable lattice or infinite-mode Fock representation. Current
analytic linked-cluster results use finite-dimensional realizations. Extending them requires the
completed-space and unbounded-operator program, not a second density-state API.

## Bloch–de Dominicis theory

The pairing theorem applies to free or quasifree Gaussian thermal states. It does not state that an
arbitrary interacting Gibbs state has a pairing-only moment expansion.

The generic pairing recursion is independent of occupation bases and finite-dimensional traces. The
current concrete instance transports algebraic Fock operators to a finite Hilbert realization and
evaluates them in the generic finite pure-point Gibbs state. A bosonic infinite-occupation instance
must state all summability, integrability, product-domain, and KMS assumptions explicitly.

## Second-quantization representations

- `AlgebraicFock Config` is a finite-support algebraic representation.
- `FiniteHilbertFock Config` is the Euclidean Hilbert realization used when `Config` is finite.
- `Fermionic.CompletedFockSpace Mode` is the completed Hilbert representation
  `ℓ²(Fermionic.Occupation Mode, ℂ)` and does not require a finite mode type.
- `Fermionic.algebraicToCompleted` embeds the finite-support fermionic core injectively with dense
  range while preserving occupation coordinates.
- `Fermionic.completedNumberOperator` is a bounded occupation-coordinate projection and agrees with
  the algebraic number operator on the full finite-support core.
- Matrix coefficients in the algebraic layer are coordinate evaluations, not automatically
  Hilbert-space inner products.
- Bosonic creation, annihilation, and number operators are generally unbounded on completed Fock
  space. They must not be exposed as bounded continuous operators without a boundedness proof.
- Infinite-mode free Hamiltonians and total number operators may be unbounded in the fermionic
  completed representation. The current free diagonal line supplies explicit `LinearPMap` domains
  and analytic results for its supported operators; completion alone does not supply such domains
  automatically.

The current boundary for completed operators, trace-class Gibbs states, finite-mode compatibility,
and later thermodynamic limits is documented in
[`roadmaps/completed-space-and-infinite-mode.md`](roadmaps/completed-space-and-infinite-mode.md).

## Assumptions by target

### Formal linked-cluster and cumulant results

- All indexing sets used by a coefficient are finite.
- Moment and cumulant families are supplied algebraically.
- Convergence and thermodynamic limits are outside the statement.

### Finite Gibbs and Bloch–de Dominicis results

- The configuration type is finite and nonempty where a normalized Gibbs state is required.
- The generic pure-point Boltzmann summability condition is automatic on the finite index.
- The algebraic operator is transported to the finite Hilbert realization before applying the
  density-state expectation.

### Infinite-dimensional density states

- The state operator is compact, positive, self-adjoint, and spectrally trace-class.
- Bounded observables are used.
- Entropy may be infinite unless an additional summability theorem applies.

### Completed infinite-mode Fock theory

- Completion is represented independently of any Hamiltonian or thermal state.
- A continuous-linear-map operator requires an explicit norm bound.
- An unbounded operator requires an explicit domain and a domain-aware operator type.
- A Gibbs state requires separate spectral or partition-weight summability hypotheses.
- Thermodynamic limits require a separately stated directed system, topology, and uniform estimates.

## Physics-to-Lean dictionary

| Physical notion | Lean counterpart | Primary module |
|---|---|---|
| Pure state representative | `QuantumTheory.State H` | `QuantumTheory/Postulates.lean` |
| Bounded observable | `QuantumTheory.Observable H` | `QuantumTheory/Postulates.lean` |
| Vector-state expectation | `QuantumTheory.expValue` | `QuantumTheory/Postulates.lean` |
| Density operator / mixed state | `QuantumTheory.DensityOperator H` | `QuantumTheory/DensityOperator.lean` |
| Density-state expectation | `DensityOperator.expectation` | `QuantumTheory/DensityOperator/Expectation.lean` |
| Pure-state projector | `QuantumTheory.pure` | `QuantumTheory/DensityOperator/Pure.lean` |
| Countable discrete POVM | `QuantumTheory.POVM H M` | `QuantumTheory/POVM/Basic.lean` |
| Born probability | `QuantumTheory.prob` | `QuantumTheory/POVM/Born.lean` |
| Von Neumann entropy | `QuantumTheory.vonNeumannEntropy` | `QuantumTheory/Entropy.lean` |
| Gibbs operator | `QuantumTheory.gibbsOp` | `QuantumTheory/Gibbs/State.lean` |
| Gibbs state | `QuantumTheory.gibbsState` | `QuantumTheory/Gibbs/State.lean` |
| Pure-point Gibbs state | `QuantumTheory.purePointGibbsDensityOperator` | `QuantumTheory/Gibbs/PurePoint.lean` |
| Finite pure-point Gibbs state | `QuantumTheory.finitePurePointGibbsDensityOperator` | `QuantumTheory/Gibbs/PurePoint.lean` |
| Energy expectation | `QuantumTheory.energyExpValue` | `QuantumTheory/Gibbs/EnergyExpectation.lean` |
| Algebraic Fock core | `SecondQuantization.Common.AlgebraicFock` | `SecondQuantization/Common/Algebra/AlgebraicFock.lean` |
| Completed fermionic Fock space | `SecondQuantization.Fermionic.CompletedFockSpace` | `SecondQuantization/Fermionic/CompletedSpace/Basic.lean` |
| Algebraic-to-completed Fock inclusion | `SecondQuantization.Fermionic.algebraicToCompleted` | `SecondQuantization/Fermionic/CompletedSpace/Basic.lean` |
| Completed single-mode number projection | `SecondQuantization.Fermionic.completedNumberOperator` | `SecondQuantization/Fermionic/CompletedSpace/Basic.lean` |
| Finite Hilbert Fock realization | `SecondQuantization.Common.FiniteHilbertFock` | `SecondQuantization/Common/Thermal/FiniteHilbertOperator.lean` |
| Finite Gibbs expectation | `SecondQuantization.Common.finiteGibbsExpectation` | `SecondQuantization/Common/Thermal/FiniteGibbsExpectationBridge.lean` |
| Perfect pairing | `Combinatorics.PerfectPairing` | `Combinatorics/PerfectPairing.lean` |
| Generic thermal pairing recursion | `ExpectationPairingRecursion` | `SecondQuantization/Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` |
