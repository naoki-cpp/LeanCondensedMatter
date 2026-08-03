# Roadmap — Quantum theory foundations (Track A)

See [the project roadmap](../roadmap.md) for the cross-track status table and
[the density-state architecture](../architecture/quantum-density-theory.md) for module ownership.

## Minimal axiomatic quantum theory

Status: `proved` for the current bounded pure-state foundation.

Implemented in `QuantumTheory/Postulates.lean`:

- `QuantumTheory.State H`: unit vectors in a complex Hilbert space;
- `QuantumTheory.Observable H`: bounded self-adjoint operators;
- `QuantumTheory.expValue`;
- reality of observable expectation values;
- invariance under multiplication of a state vector by a unit complex phase.

A quotient of unit vectors by global phase is not formalized. The current `State` type stores
representatives.

## Density operators, expectations, and purity

Status: `proved`.

`QuantumTheory.DensityOperator H` is the canonical dimension-independent mixed-state type. It is a
positive bounded operator with bundled compact self-adjoint spectral trace-class data and spectral
trace `1`.

Implemented results include:

- the rank-one pure-state embedding `QuantumTheory.pure`;
- the normalized continuous-linear expectation functional `DensityOperator.expectation`;
- normalization, contractivity, positivity, and reality theorems for expectations;
- construction from finite-dimensional positive trace-one operators;
- equality with the ordinary matrix trace in finite dimensions;
- diagonal expectation formulas;
- spectral purity `QuantumTheory.purity ρ = ∑' i, λᵢ²`;
- `0 ≤ purity ρ ≤ 1`;
- `purity (pure ψ) = 1`;
- the exact identity `ρ.expectation ρ.op = (purity ρ : ℂ)`;
- the finite-dimensional formula `Tr(ρ²) = (purity ρ : ℂ)`.

A converse characterization of `purity ρ = 1` as rank one is not part of the current API.

## Discrete POVMs and the Born rule

Status: `proved` for countable discrete outcomes.

`QuantumTheory.POVM H M` accepts any countable outcome type and uses strong pointwise normalization
of its effects. The Born probability is represented first as a self-adjoint scalar and then as a
real number.

Implemented results include:

- nonnegativity;
- probability at most `1`;
- summability over countable outcomes;
- total probability `1`;
- finite-outcome normalization as a specialization of the same theorem.

Continuous-outcome measurements and measure-valued POVMs are outside the current API.

## Von Neumann entropy

Status: `proved` for the spectral definition and its finite-dimensional specialization.

`QuantumTheory.vonNeumannEntropy` is `ENNReal`-valued because a normalized trace-class density
operator can have infinite entropy. The implementation includes:

- nonnegative density eigenvalues bounded by `1`;
- the compact entropy operator `entropyOp ρ = -ρ log ρ` from continuous functional calculus;
- equality between the entropy eigenvalue sum and the spectral trace of the entropy operator under
  the required summability hypothesis;
- diagonal entropy formulas;
- automatic entropy finiteness and real-valued `.toReal` formulas in finite dimensions.

Boltzmann’s principle, identifying `k_B` times this quantity with thermodynamic entropy, remains a
physical postulate outside the formalized mathematical theory.

## Gibbs states and Helmholtz free energy

Status: `proved` for bounded Hamiltonians under explicit compactness and summability hypotheses.

Implemented in `QuantumTheory/Gibbs/`:

- `gibbsOp Hop β = exp (-β Hop)` through continuous functional calculus;
- positivity of `gibbsOp`;
- normalized `gibbsState` when its spectral trace is defined and nonzero;
- `energyExpectationSelfAdjoint` and the lossless real value `energyExpValue`;
- `ρ.expectation Hop.1 = (energyExpValue ρ Hop : ℂ)`;
- the finite-dimensional identity `Tr(ρH) = (energyExpValue ρ Hop : ℂ)`;
- the Helmholtz free-energy lower bound;
- entropy finiteness under the variational hypotheses;
- the Gibbs-state entropy identity and attainment of the lower bound.

The present bounded-Hamiltonian assumptions imply finite dimensionality whenever `gibbsOp` is
compact. A genuine infinite-dimensional Gibbs theory therefore requires an unbounded self-adjoint
Hamiltonian, compact-resolvent or semigroup hypotheses, and explicit operator-domain control.

The uniqueness statement “equality holds only for the Gibbs state” remains open.

## Current next steps

1. Prove uniqueness of the Gibbs free-energy minimizer.
2. Design an unbounded Hamiltonian interface supporting genuine infinite-dimensional Gibbs states.
3. Connect the canonical density-state expectation to completed Fock-space and KMS constructions.
4. Decide whether the rank-one characterization of maximal purity warrants a focused theorem issue.
5. Add continuous-outcome measurement theory only after a measure-theoretic API is designed.
