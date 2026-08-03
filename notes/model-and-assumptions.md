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

The Helmholtz free-energy theorem proves the Gibbs lower bound under these hypotheses, and the Gibbs
state satisfies the corresponding entropy identity. Uniqueness of the minimizer is not yet proved.

A bounded Hamiltonian cannot model a genuinely infinite-dimensional compact Gibbs operator: the
operator exponential is invertible, so compactness forces finite dimensionality. Infinite-volume or
infinite-mode Gibbs theory therefore requires an unbounded self-adjoint Hamiltonian or a semigroup
interface with domain control.

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
current concrete instance is a finite Gibbs realization. A bosonic infinite-occupation instance
must state all summability, integrability, product-domain, and KMS assumptions explicitly.

## Second-quantization representations

- `AlgebraicFock Config` is a finite-support algebraic representation.
- `FiniteHilbertFock Config` is the Euclidean Hilbert realization used when `Config` is finite.
- Matrix coefficients in the algebraic layer are coordinate evaluations, not automatically
  Hilbert-space inner products.
- Bosonic creation, annihilation, and number operators are generally unbounded on completed Fock
  space. They must not be exposed as bounded continuous operators without a boundedness proof.

## Assumptions by target

### Formal linked-cluster and cumulant results

- All indexing sets used by a coefficient are finite.
- Moment and cumulant families are supplied algebraically.
- Convergence and thermodynamic limits are outside the statement.

### Finite Gibbs and Bloch–de Dominicis results

- The configuration type is finite and nonempty where a normalized finite Gibbs state is required.
- Boltzmann weights are real and positive.
- The algebraic operator is transported to the finite Hilbert realization before applying the
  density-state expectation.

### Infinite-dimensional density states

- The state operator is compact, positive, self-adjoint, and spectrally trace-class.
- Bounded observables are used.
- Entropy may be infinite unless an additional summability theorem applies.

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
| Energy expectation | `QuantumTheory.energyExpValue` | `QuantumTheory/Gibbs/EnergyExpectation.lean` |
| Finite Hilbert Fock realization | `SecondQuantization.Common.FiniteHilbertFock` | `SecondQuantization/Common/Thermal/FiniteGibbsDensityOperator.lean` |
| Finite Gibbs expectation | `SecondQuantization.Common.finiteGibbsExpectation` | `SecondQuantization/Common/Thermal/FiniteGibbsDensityOperator.lean` |
| Perfect pairing | `Combinatorics.PerfectPairing` | `Combinatorics/PerfectPairing.lean` |
| Generic thermal pairing recursion | `ExpectationPairingRecursion` | `SecondQuantization/Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean` |
