# Quantum theory foundations (Track A)

See [the project roadmap](../roadmap.md) for cross-track status and
[the density-state architecture](../architecture/quantum-density-theory.md) for ownership.

## Minimal bounded theory

Status: `proved`.

`QuantumTheory/Postulates.lean` defines normalized state-vector representatives, with
`QuantumTheory.StateVector` as the canonical name and `QuantumTheory.State` as its compatibility name,
together with bounded self-adjoint observables. The public expectation API provides the canonical
complex vector-state expectation, a lossless real observable expectation, reality, and global-phase
invariance.

## Bounded one-particle dynamics

Status: `proved` and dimension-independent.

For a bounded self-adjoint `H₀` and `ℏ > 0`, the linear-response dynamics layer provides

```text
U₀(t) = exp (-(i t / ℏ) H₀),
```

with unitarity, norm preservation, Schrödinger-picture state evolution, Heisenberg observable
evolution, density-operator evolution, exact pure/density expectation equivalence between pictures,
and restriction of density evolution to physical `PureState` values.

The equations-of-motion layer proves bounded Schrödinger, Heisenberg, and von Neumann equations in
operator/norm differentiable form. Conservation results show that observables commuting with `H₀`
have stationary expectations and density operators commuting with `H₀` are fixed by the free
evolution.

Reusable unitary-conjugation facts for compact spectral trace-class operators live under
`Analysis/Operator/TraceClass/` rather than in the physics layer.

## Density operators, physical pure states, expectations, and purity

Status: `proved` for the current spectral trace-class density model and density-backed physical pure
states.

`QuantumTheory.DensityOperator H` bundles a positive bounded operator with compact self-adjoint
spectral trace-class data and spectral trace `1`. `QuantumTheory.PureState H` is the subtype of density
operators represented by some normalized state vector through `QuantumTheory.pure`. The API includes:

- the rank-one embedding `QuantumTheory.pure` and `PureState.ofStateVector`;
- existence of a normalized vector representative for every `PureState`;
- equivalence between equality of normalized rank-one density operators and unit-modulus global-phase
  equivalence of their representatives, together with the corresponding `PureState.ofStateVector`
  equality theorem;
- physical-pure-state observable expectations defined through the canonical density expectation and
  agreement with representative-level `observableExpValue`;
- bounded unitary evolution of `PureState`, preservation of the pure-density predicate, and exact
  agreement with representative evolution;
- normalized complex and lossless real observable expectations;
- positivity, reality, contractivity, and countable Hilbert-basis formulas;
- a positive square root with Hilbert--Schmidt control and the corresponding `innerHS` expectation
  identity;
- finite-dimensional matrix-trace specializations;
- spectral purity with `0 ≤ purity ρ ≤ 1`, `purity (pure ψ) = 1`, and the dimension-independent
  characterization `IsPureDensity ρ ↔ purity ρ = 1`;
- the finite-dimensional `Tr(ρ²)` formula as a specialization of the same purity API.

The maximal-purity converse uses the existing compact self-adjoint spectral reconstruction and does
not require an additional finite-dimensional assumption. An explicit one-dimensional-range predicate
is not needed for this characterization and should be added only if it has independent downstream
use. A projective/ray presentation remains optional rather than the storage type.

## Discrete POVMs and Born probabilities

Status: `proved` for countable discrete outcomes.

`QuantumTheory.POVM H M` uses strong pointwise normalization. Born probabilities have canonical
nonnegative `NNReal` values, are summable with total probability `1`, and are packaged as
`bornPMF P ρ : PMF M`. The real-valued compatibility view is derived from the same probability rather
than by taking an arbitrary complex real part.

Continuous-outcome POVMs, instruments, and state-update theory remain open.

## Von Neumann entropy

Status: `proved` for the spectral definition and finite-dimensional specialization.

`QuantumTheory.vonNeumannEntropy` is `ENNReal`-valued because a trace-one density operator can have
infinite entropy. The theory provides the compact entropy operator, spectral/diagonal formulas, and
finite-dimensional real-valued formulas after finiteness is established. Multiplication by `k_B` and
identification with thermodynamic entropy is a separate physical postulate.

## Gibbs states and Helmholtz free energy

Status: `proved` for bounded Hamiltonians under explicit compactness and summability hypotheses.

The Gibbs layer provides `gibbsOp`, normalized Gibbs states, energy expectation, common-eigenbasis
formulas, the Helmholtz free-energy lower bound, the Gibbs entropy identity, attainment of the bound,
and the equality/uniqueness characterization of the Gibbs minimizer.

A bounded Hamiltonian cannot produce a genuinely infinite-dimensional compact invertible Gibbs
operator. Infinite-dimensional Gibbs theory therefore requires an unbounded self-adjoint Hamiltonian
or semigroup/resolvent framework with explicit domains.

## Open work

- add an explicit one-dimensional-range characterization of physical pure states only if downstream
  proofs need that formulation;
- add a projective/ray presentation only if it materially improves public use without duplicating
  expectation or dynamics theory;
- extend the Hamiltonian interface to genuine infinite-dimensional Gibbs states;
- reuse the canonical density expectation throughout completed Fock/KMS and response layers;
- add continuous-outcome measurement theory after a measure-theoretic operator-valued API is fixed.
