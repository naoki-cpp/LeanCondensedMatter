# Quantum density-state architecture

This document is the source of truth for the project’s density-state, measurement, entropy, and
bounded Gibbs-state APIs.

## Canonical state model

`QuantumTheory.DensityOperator H` is the only mixed-state type. It contains:

- a bounded operator `op : H →L[ℂ] H`;
- positivity of `op`;
- a bundled compact self-adjoint spectral trace-class witness;
- normalization of the spectral trace to `1`.

The type is dimension-independent. Finite dimensionality is an additional typeclass hypothesis used
only by specialization theorems.

The canonical modules are:

```text
QuantumTheory/
├── DensityOperator.lean
├── DensityOperator/
│   ├── Basic.lean
│   ├── Pure.lean
│   ├── Purity.lean
│   ├── Expectation.lean
│   ├── ExpectationOrder.lean
│   └── Diagonal.lean
├── POVM/
│   ├── Basic.lean
│   └── Born.lean
├── Entropy.lean
├── Entropy/
│   ├── Basic.lean
│   └── Diagonal.lean
├── FiniteDimensional/
│   ├── DensityOperator.lean
│   ├── Expectation.lean
│   ├── Purity.lean
│   └── Entropy.lean
└── Gibbs/
    ├── State.lean
    ├── EnergyExpectation.lean
    ├── FreeEnergy.lean
    ├── Entropy.lean
    ├── DiagonalEnergy.lean
    └── Variational.lean
```

`QuantumTheory/DensityOperator.lean` and `QuantumTheory/Entropy.lean` are public umbrella modules.

## Expectations

`DensityOperator.expectation` is a continuous complex-linear functional on bounded operators. It is
defined from the density operator’s spectral decomposition and supplies:

- complex linearity;
- normalization on the identity;
- a norm bound;
- nonnegativity on positive operators;
- reality on symmetric, self-adjoint, or positive operators.

In finite dimensions, `DensityOperator.expectation_eq_linearMap_trace` identifies this definition
with the ordinary matrix trace `Tr(ρA)`. Diagonal finite-sum formulas are specialization theorems of
the same expectation.

Real-valued physical quantities are obtained from a proved self-adjoint complex scalar through
`Complex.selfAdjointEquiv`; they are not defined by discarding an arbitrary imaginary part.

## Pure states and purity

`QuantumTheory.pure` maps a unit vector to the rank-one projector `|ψ⟩⟨ψ|` and proves that it is a
normalized density operator on an arbitrary complete complex Hilbert space. This is a pure-state
embedding, not purification of a mixed state on a larger space.

`QuantumTheory.purity ρ` is the convergent spectral sum `∑ᵢ λᵢ²`. The API proves

```text
0 ≤ purity ρ ≤ 1
purity (pure ψ) = 1
ρ.expectation ρ.op = (purity ρ : ℂ)
```

In finite dimensions, `Tr(ρ²) = (purity ρ : ℂ)` exactly.

## Discrete measurements

`QuantumTheory.POVM H M` supports any countable outcome type. Each effect is positive and the effects
sum strongly to the identity:

```lean
hasSum_apply : ∀ x, HasSum (fun m => E m x) x
```

`probSelfAdjoint` records the Born expectation as a self-adjoint complex scalar. `prob` transports it
to `ℝ` through `Complex.selfAdjointEquiv`. The API proves nonnegativity, the upper bound `≤ 1`,
summability over outcomes, and total probability `1`. Finite-outcome sums use the same POVM type.

## Entropy

`QuantumTheory.vonNeumannEntropy` is `ENNReal`-valued. This codomain represents both finite entropy
and genuine divergence in infinite dimensions without assigning a junk real value to a divergent
series.

`entropyOp ρ = -ρ log ρ` is defined by continuous functional calculus and is compact. When its
nonzero eigenvalues are summable, its spectral trace equals the entropy eigenvalue sum. In finite
dimensions entropy is automatically finite, and `.toReal` agrees with the finite sum of
`Real.negMulLog` over eigenvalues or diagonal weights.

## Gibbs states and free energy

For a bounded self-adjoint Hamiltonian `Hop`, `gibbsOp Hop β` is defined by continuous functional
calculus as `exp (-β Hop)`. `gibbsState` normalizes this operator when compactness, spectral
summability, and nonzero spectral trace are supplied.

The current bounded-Hamiltonian model has an important limitation: compactness of `gibbsOp Hop β`
forces the Hilbert space to be finite-dimensional because the exponential is invertible. Genuine
infinite-dimensional Gibbs states therefore require a later unbounded self-adjoint Hamiltonian and
domain-aware theory.

The bounded theory includes:

- `energyExpectationSelfAdjoint`, the self-adjoint scalar representing `Tr(ρH)`;
- `energyExpValue`, its lossless real image under `Complex.selfAdjointEquiv`;
- the exact identity `ρ.expectation Hop.1 = (energyExpValue ρ Hop : ℂ)`;
- the Helmholtz free-energy lower bound;
- finiteness of entropy under the variational hypotheses;
- the entropy/free-energy identity for the normalized Gibbs state.

Uniqueness of the Gibbs minimizer is not yet formalized.

## Finite-dimensional specialization

Finite-dimensional code uses the same `DensityOperator` type. The specialization layer provides:

- `DensityOperator.ofFiniteDimensional`;
- equivalence with ordinary `LinearMap.trace` normalization;
- ordinary trace formulas for expectations;
- finite diagonal expectation formulas;
- the exact matrix formula `Tr(ρ²) = (purity ρ : ℂ)`;
- the exact energy formula `Tr(ρH) = (energyExpValue ρ Hop : ℂ)`;
- automatic entropy summability and finiteness.

There is no separate finite-dimensional state or measurement model.

## Scope boundaries

The current API does not provide:

- continuous-outcome or measure-valued POVMs;
- a general Schatten ideal hierarchy;
- a trace on arbitrary non-self-adjoint trace-class operators;
- unbounded observables or Hamiltonians;
- thermodynamic limits;
- completed infinite-mode Fock-space domain theory.

Those extensions must build on the canonical state and expectation APIs rather than introduce
parallel public state types.
