# Quantum density-state architecture

This note records the stable density-state, measurement, entropy, and bounded Gibbs-state architecture.
Lean declarations are authoritative for mathematical semantics; the Python architecture audits enforce
ownership, dependency, dimension, and selected semantic-safety boundaries without pinning incidental
proof text.

## Canonical state model

`QuantumTheory.DensityOperator H` is the unique mixed-state type. It contains a bounded operator,
positivity, a bundled compact self-adjoint spectral trace-class witness, and normalization of the
spectral trace to `1`.

The type is dimension-independent. Finite dimensionality is introduced only at theorem boundaries that
actually require an ordinary finite matrix trace or another genuinely finite construction.

Canonical ownership is feature-based:

- `QuantumTheory/Postulates.lean` owns pure states, bounded observables, and vector-state expectations;
- `QuantumTheory/DensityOperator/` owns mixed-state construction, expectation, purity, diagonal
  formulas, and finite-dimensional specializations;
- `QuantumTheory/POVM/` owns countable discrete measurements and Born probabilities;
- `QuantumTheory/Entropy/` owns von Neumann entropy and its diagonal/finite specializations;
- `QuantumTheory/Gibbs/` owns bounded Gibbs states, energy and free-energy results, entropy,
  equality/minimizer uniqueness, diagonal formulas, and pure-point Gibbs constructions.

`QuantumTheory/DensityOperator.lean` and `QuantumTheory/Entropy.lean` are public umbrella modules.
Finite-dimensional specializations remain with the feature they specialize rather than forming a
parallel finite-dimensional state hierarchy.

## Pure-state expectations

The Lean API defines the canonical complex expectation

```lean
expValue A ψ = inner ℂ ψ (A ψ)
```

and proves that for a self-adjoint observable it agrees with the reversed inner-product orientation.
The real observable value is obtained losslessly from a proved self-adjoint complex scalar through
`Complex.selfAdjointEquiv`:

```lean
observableExpValue A ψ : ℝ
```

The API also proves the exact complex recovery theorem and global-phase invariance. These are Lean
semantics, not source-text patterns that architecture CI needs to freeze.

## Mixed-state expectations

`DensityOperator.expectation` is the canonical complex-linear expectation functional on bounded
operators. For `Observable H`,

```lean
DensityOperator.observableExpectation : ℝ
```

is the canonical real-valued mixed-state API, with an exact embedding theorem back into the complex
expectation.

For a rank-one density operator, the complex and real density-state expectations agree with the
corresponding vector-state expectations.

Architecture CI enforces unique ownership of the public pure-state and density-state real expectation
APIs. It does not require a particular proof helper or literal implementation body.

## Countable diagonal foundation

The generic diagonal theory is countable rather than finite-dimensional. The square-root layer owns

```lean
DensityOperator.sqrtOp
DensityOperator.sqrtOp_isHilbertSchmidt
DensityOperator.expectation_eq_innerHS
```

and the diagonal-formula layer owns the `HasSum`, `Summable`, complex `tsum`, and real observable
`tsum` formulas.

These modules must remain free of accidental `[FiniteDimensional ...]` and `[Fintype ...]`
assumptions. The density umbrella exports the canonical diagonal bridge and formula modules.

For a Hamiltonian, `Gibbs/DiagonalEnergy.lean` exposes the countable common-eigenbasis
`HilbertBasis`/`tsum` theorem as the generic foundation. Architecture CI requires that foundation to
exist, but it does not inspect the proof strategy used by a finite corollary.

## Discrete measurements

`QuantumTheory.POVM H M` supports countable outcome types. The scalar boundary is intentionally split
into semantic types:

- `probSelfAdjoint P ρ m : selfAdjoint ℂ` for the proved-real complex expectation;
- `probNNReal P ρ m : NNReal` as the canonical nonnegative probability;
- `prob P ρ m : ℝ` as a compatibility coercion;
- `bornPMF P ρ : PMF M` as the normalized countable family.

Architecture CI enforces unique ownership of `probNNReal` and `bornPMF`. It also retains one semantic
safety guard for the internal probability kernel: physical real values must flow through
`diagonalExpectationValue` and must not be defined by directly discarding an imaginary component with
`.re`.

This is different from a proof snapshot. The check protects a deliberately lossless physical-scalar
boundary rather than a particular theorem sequence.

## Entropy

`QuantumTheory.vonNeumannEntropy` is `ENNReal`-valued so genuine divergence can be represented without
a junk finite value. `entropyOp ρ = -ρ log ρ` is defined through continuous functional calculus. In
finite dimensions entropy is automatically finite and the finite formulas are feature-owned
specializations of the same state model.

## Gibbs states and free energy

For a bounded self-adjoint Hamiltonian `Hop`, `gibbsOp Hop β` is defined by continuous functional
calculus as `exp (-β Hop)`. `gibbsState` normalizes this operator when compactness, spectral
summability, and nonzero spectral trace are supplied.

For `β > 0`, the Helmholtz lower bound is attained exactly by the canonical Gibbs state under those
hypotheses. Pure-point spectral data provide a separate state-level Gibbs construction when the
Boltzmann weights are summable.

The bounded model has the known limitation that compactness of this invertible exponential forces
finite dimensionality. Genuine infinite-dimensional Gibbs states therefore require the separate
unbounded/domain-aware line or explicit pure-point spectral data.

`energyExpValue` is the Hamiltonian-facing observable expectation API. The Lean library proves its
relation to the generic expectation and its diagonal formulas. Architecture CI protects ownership and
the countable diagonal foundation, not the exact source expression used to define or prove each
specialization.

## Finite-dimensional specialization

Finite-dimensional code uses the same `DensityOperator` type. `DensityOperator/Finite.lean` and
`Entropy/Finite.lean` provide the ordinary trace and finite-sum specializations. There is no parallel
finite-dimensional state or measurement hierarchy.

The guiding rule is:

```text
dimension-independent state/expectation semantics
                ↓
countable spectral/diagonal foundation
                ↓
finite-dimensional corollaries where finiteness is genuinely required
```

## CI-enforced architecture boundary

`scripts/check_quantum_theory_architecture.py` enforces durable current-state invariants:

- unique canonical ownership of `DensityOperator` and `POVM`;
- unique canonical ownership of pure-state and density-state real observable expectations;
- unique canonical ownership of `probNNReal` and `bornPMF`;
- the lossless Born probability-kernel boundary;
- ownership of the Hilbert-Schmidt diagonal bridge and countable diagonal formulas;
- absence of finite-dimensional/index assumptions from the generic countable diagonal modules;
- export of the canonical diagonal modules from the density umbrella;
- presence of the countable Gibbs diagonal-energy foundation.

Other architecture audits additionally enforce the project-wide physical-scalar boundary and the
upstream dependency rule that `QuantumTheory` must not import `SecondQuantization`.

The architecture audits intentionally do **not** require:

- exact definition bodies;
- `simpa using ...` or other proof fragments;
- helper theorem names merely because a current proof happens to use them;
- historical lists of retired modules, aliases, or former owners.

If a mathematical identity itself is important, it belongs as a Lean theorem. Python architecture CI
should protect ownership, layering, type-level assumptions, and semantic safety properties that are
not naturally expressed by merely compiling the library.

## Scope boundaries

The current API does not yet provide a general continuous-outcome POVM theory, a full Schatten-ideal
hierarchy, arbitrary non-self-adjoint trace-class operators, unbounded observables in the bounded core,
or thermodynamic limits. Those extensions should build on the canonical state and expectation APIs
rather than introduce parallel public state types.
