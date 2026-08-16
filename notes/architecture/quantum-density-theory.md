# Quantum density-state architecture

This document is the source of truth for the project’s density-state, measurement, entropy, and
bounded Gibbs-state APIs.

## Canonical state model

`QuantumTheory.DensityOperator H` is the only mixed-state type. It contains:

- a bounded operator `op : H →L[ℂ] H`;
- positivity of `op`;
- a bundled compact self-adjoint spectral trace-class witness;
- normalization of the spectral trace to `1`.

The type is dimension-independent. Finite dimensionality is an additional hypothesis only where an
ordinary finite matrix trace or another genuinely finite construction is used.

The canonical modules are:

```text
QuantumTheory/
├── Postulates.lean
├── DensityOperator.lean
├── DensityOperator/
│   ├── Basic.lean
│   ├── Pure.lean
│   ├── Purity.lean
│   ├── Expectation.lean
│   ├── ExpectationOrder.lean
│   ├── ObservableExpectation.lean
│   ├── Diagonal.lean
│   ├── DiagonalExpectation.lean
│   ├── DiagonalFormula.lean
│   └── Finite.lean
├── POVM/
│   ├── Basic.lean
│   └── Born.lean
├── Entropy.lean
├── Entropy/
│   ├── Basic.lean
│   ├── Diagonal.lean
│   └── Finite.lean
└── Gibbs/
    ├── State.lean
    ├── EnergyExpectation.lean
    ├── FreeEnergy.lean
    ├── Entropy.lean
    ├── DiagonalEnergy.lean
    └── Variational.lean
```

`QuantumTheory/DensityOperator.lean` and `QuantumTheory/Entropy.lean` are public umbrella modules.
Finite-dimensional specializations live with the feature they specialize rather than in a parallel
`FiniteDimensional/` hierarchy.

## Expectations

The pure-state complex expectation uses the canonical physicists’ orientation

```lean
expValue A ψ = inner ℂ ψ (A ψ).
```

For a self-adjoint observable this equals the formerly used reversed orientation
`inner ℂ (A ψ) ψ`. `observableExpValue A ψ : ℝ` transports the proved-real complex scalar through
`Complex.selfAdjointEquiv`, and both values are invariant under global phase.

`DensityOperator.expectation` is a continuous complex-linear functional on arbitrary bounded
operators. It is defined from the density operator’s spectral decomposition and supplies complex
linearity, normalization on the identity, a norm bound, nonnegativity on positive operators, and
reality on symmetric, self-adjoint, or positive operators.

For an `Observable H`, `DensityOperator.observableExpectation : ℝ` is the canonical real-valued
mixed-state API. Its exact boundary theorem is

```lean
ρ.expectation A.1 = (ρ.observableExpectation A : ℂ).
```

For a rank-one density operator, the complex and real APIs agree exactly with the corresponding
vector-state expectations:

```lean
(pure ψ).expectation A.1 = expValue A ψ
(pure ψ).observableExpectation A = observableExpValue A ψ.
```

### Countable diagonal formulas

`DensityOperator.sqrtOp ρ = cfc Real.sqrt ρ.op` is the positive square root of the density
operator. Trace-one spectral summability proves

```lean
DensityOperator.sqrtOp_isHilbertSchmidt : IsHilbertSchmidt ρ.sqrtOp.
```

This yields the basis-independent bridge for every bounded operator `A` and every Hilbert basis
`b`:

```lean
ρ.expectation A = innerHS b ρ.sqrtOp (A * ρ.sqrtOp).
```

The right side is an absolutely convergent Hilbert–Schmidt pairing. Consequently, whenever `b`
diagonalizes `ρ` with real weights `w`, no finite-dimensional hypothesis is needed for

```lean
ρ.expectation A = ∑' i, (w i : ℂ) * inner ℂ (b i) (A (b i)).
```

The implementation also exposes the corresponding `HasSum` and `Summable` theorems. For a
self-adjoint observable, the lossless real specialization is

```lean
ρ.observableExpectation A =
  ∑' i, w i * diagonalExpectationValue A.1 A.2 (b i).
```

The real theorem is obtained by transporting an already identified real complex series; the
physical value is not defined by applying `.re` to an arbitrary scalar.

In finite dimensions, `DensityOperator.expectation_eq_linearMap_trace` additionally identifies the
complex functional with the ordinary matrix trace `Tr(ρA)`. Finite-sum formulas are corollaries of
the countable diagonal foundation whenever a finite Hilbert basis is supplied.

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

The Born scalar boundary is represented in four deliberately distinct forms:

- `probSelfAdjoint P ρ m : selfAdjoint ℂ` records the proved-real complex expectation
  `Tr(ρ Eₘ)`;
- `probNNReal P ρ m : NNReal` is the canonical scalar probability and expresses nonnegativity in
  its type;
- `prob P ρ m : ℝ` is only the compatibility coercion of `probNNReal`;
- `bornPMF P ρ : PMF M` packages the whole countable family as a normalized probability mass
  function.

The exact complex boundary theorem is

```lean
ρ.expectation (P.E m) = ((probNNReal P ρ m : ℝ) : ℂ).
```

The internal double-series kernel uses `diagonalExpectationValue` for every positive effect, so its
physical real value is transported through a self-adjointness proof rather than defined by applying
`.re` to an arbitrary complex expression. Uses of `Complex.reCLM` inside normalization proofs are
proof-only transport of already identified real scalars and do not define the probability API.

The API proves nonnegativity, the upper bound `≤ 1`, countable summability, total probability `1`,
and finite-outcome normalization. Both `NNReal` and compatibility `ℝ` normalization theorems are
available, while `bornPMF` carries normalization intrinsically.

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

- `energyExpValue ρ Hop`, the Hamiltonian-facing specialization of
  `ρ.observableExpectation Hop`;
- the exact identity `ρ.expectation Hop.1 = (energyExpValue ρ Hop : ℂ)` inherited from the generic
  observable boundary;
- the countable common-eigenbasis formula

  ```lean
  energyExpValue ρ Hop = ∑' i, w i * E i;
  ```

- the finite common-eigenbasis sum as a direct corollary of the countable theorem;
- the Helmholtz free-energy lower bound;
- finiteness of entropy under the variational hypotheses;
- the entropy/free-energy identity for the normalized Gibbs state.

The finite common-eigenbasis corollary needs a finite index type but no separate
`FiniteDimensional ℂ H` hypothesis once a complete finite orthonormal basis is explicitly supplied.

Uniqueness of the Gibbs minimizer is not yet formalized.

## Finite-dimensional specialization

Finite-dimensional code uses the same `DensityOperator` type. Feature-owned specialization modules
`DensityOperator/Finite.lean` and `Entropy/Finite.lean` provide:

- `DensityOperator.ofFiniteDimensional`;
- equivalence with ordinary `LinearMap.trace` normalization;
- ordinary trace formulas for expectations;
- finite diagonal expectation formulas derived directly from the countable `HilbertBasis` theory;
- the exact matrix formula `Tr(ρ²) = (purity ρ : ℂ)`;
- the exact energy formula `Tr(ρH) = (energyExpValue ρ Hop : ℂ)`;
- automatic entropy summability and finiteness.

There is no separate finite-dimensional state, measurement model, or top-level finite-dimensional
module hierarchy.

## Regression boundary

The QuantumTheory architecture audit enforces:

- the canonical pure-state orientation `inner ℂ ψ (A ψ)`;
- unique ownership of `observableExpValue` in `Postulates.lean`;
- unique ownership of `DensityOperator.observableExpectation` in
  `DensityOperator/ObservableExpectation.lean`;
- `energyExpValue` remaining a direct thermodynamic specialization rather than a duplicate generic
  implementation;
- unique ownership of `probNNReal` and `bornPMF` in `POVM/Born.lean`;
- `prob` remaining a direct real coercion of `probNNReal`;
- the Born normalization kernel using `diagonalExpectationValue` and containing no direct `.re`
  projection in its definition body;
- ownership of the density square-root/Hilbert–Schmidt bridge in
  `DensityOperator/DiagonalExpectation.lean`;
- ownership of countable complex and real diagonal formulas in
  `DensityOperator/DiagonalFormula.lean`;
- absence of `Fintype` and `FiniteDimensional` assumptions from the generic countable diagonal
  modules;
- finite-dimensional density and entropy specializations remaining feature-owned rather than
  rebuilding a parallel `FiniteDimensional/` hierarchy;
- `Gibbs/DiagonalEnergy.lean` retaining the `HilbertBasis`/`tsum` theorem as its foundation, with
  the finite sum delegating to it instead of rebuilding the result through matrix trace.

Proof-local extraction of the real component of a proved equality remains allowed. The audit guards
public physical definitions and canonical internal kernels, not ordinary proof techniques.

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
