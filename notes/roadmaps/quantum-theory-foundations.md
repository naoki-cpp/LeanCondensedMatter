# Roadmap — Quantum theory foundations (Track A)

See [the project roadmap](../roadmap.md) for the cross-track status table and
[the density-state architecture](../architecture/quantum-density-theory.md) for module ownership.

## Minimal axiomatic quantum theory

Status: `proved` for the current bounded pure-state foundation.

Implemented in `QuantumTheory/Postulates.lean`:

- `QuantumTheory.State H`: unit vectors in a complex Hilbert space;
- `QuantumTheory.Observable H`: bounded self-adjoint operators;
- the canonical complex expectation `QuantumTheory.expValue A ψ = inner ℂ ψ (A ψ)`;
- exact agreement with the formerly used reversed orientation `inner ℂ (A ψ) ψ`;
- the lossless real observable expectation `QuantumTheory.observableExpValue`;
- reality of observable expectation values;
- invariance of both complex and real expectations under multiplication of a state vector by a
  unit complex phase.

A quotient of unit vectors by global phase is not formalized. The current `State` type stores
representatives.

## Density operators, expectations, and purity

Status: `proved`.

`QuantumTheory.DensityOperator H` is the canonical dimension-independent mixed-state type. It is a
positive bounded operator with bundled compact self-adjoint spectral trace-class data and spectral
trace `1`.

Implemented results include:

- the rank-one pure-state embedding `QuantumTheory.pure`;
- the normalized continuous-linear complex expectation functional `DensityOperator.expectation`;
- the lossless real observable expectation `DensityOperator.observableExpectation`;
- the exact coercion identity
  `ρ.expectation A.1 = (ρ.observableExpectation A : ℂ)`;
- agreement of pure vector-state and rank-one density-state expectations, both complex and real;
- normalization, contractivity, positivity, and reality theorems for expectations;
- the positive square root `DensityOperator.sqrtOp ρ = cfc Real.sqrt ρ.op`;
- `DensityOperator.sqrtOp_isHilbertSchmidt` from trace-one spectral summability;
- the basis-independent identity
  `ρ.expectation A = innerHS b ρ.sqrtOp (A * ρ.sqrtOp)`;
- absolutely convergent countable `HilbertBasis` formulas for arbitrary bounded operators;
- lossless real countable diagonal formulas for observables through `diagonalExpectationValue`;
- construction from finite-dimensional positive trace-one operators;
- equality with the ordinary matrix trace in finite dimensions;
- finite diagonal formulas as specializations of the countable theory;
- spectral purity `QuantumTheory.purity ρ = ∑' i, λᵢ²`;
- `0 ≤ purity ρ ≤ 1`;
- `purity (pure ψ) = 1`;
- the exact identity `ρ.expectation ρ.op = (purity ρ : ℂ)`;
- the finite-dimensional formula `Tr(ρ²) = (purity ρ : ℂ)`.

A converse characterization of `purity ρ = 1` as rank one is not part of the current API.

## Discrete POVMs and the Born rule

Status: `proved` for countable discrete outcomes with physically typed probabilities.

`QuantumTheory.POVM H M` accepts any countable outcome type and uses strong pointwise normalization
of its effects. The Born expectation is first represented as a self-adjoint complex scalar, then
transported losslessly to the canonical nonnegative value
`probNNReal P ρ m : NNReal`.

Implemented results include:

- the exact complex boundary
  `ρ.expectation (P.E m) = ((probNNReal P ρ m : ℝ) : ℂ)`;
- `prob P ρ m : ℝ` as a compatibility coercion of `probNNReal`;
- a normalization kernel defined through `diagonalExpectationValue`, with no direct `.re`
  projection in the physical definition;
- nonnegativity and probability at most `1`;
- summability over countable outcomes in both `NNReal` and compatibility `ℝ` forms;
- total probability `1`;
- `bornPMF P ρ : PMF M`, which packages the countable normalized Born distribution;
- finite-outcome normalization as a specialization of the same countable theorem.

Proof-local use of `Complex.reCLM` only transports an already identified real equality and is not the
definition of a physical probability. Continuous-outcome measurements and measure-valued POVMs are
outside the current API.

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
- `energyExpValue ρ Hop`, retained as the Hamiltonian-facing specialization of
  `ρ.observableExpectation Hop`;
- `ρ.expectation Hop.1 = (energyExpValue ρ Hop : ℂ)` through the generic observable coercion theorem;
- the countable common-eigenbasis identity
  `energyExpValue ρ Hop = ∑' i, w i * E i`;
- the finite common-eigenbasis sum as a direct corollary of the countable theorem;
- the finite-dimensional identity `Tr(ρH) = (energyExpValue ρ Hop : ℂ)`;
- the Helmholtz free-energy lower bound;
- entropy finiteness under the variational hypotheses;
- the Gibbs-state entropy identity and attainment of the lower bound.

The present bounded-Hamiltonian assumptions imply finite dimensionality whenever `gibbsOp` is
compact. A genuine infinite-dimensional Gibbs theory therefore requires an unbounded self-adjoint
Hamiltonian, compact-resolvent or semigroup hypotheses, and explicit operator-domain control.

The uniqueness statement “equality holds only for the Gibbs state” remains open.

## Current next steps

1. Extend the physical-scalar architecture audit from canonical APIs to new public definitions.
2. Prove uniqueness of the Gibbs free-energy minimizer.
3. Design an unbounded Hamiltonian interface supporting genuine infinite-dimensional Gibbs states.
4. Connect the canonical density-state expectation to completed Fock-space and KMS constructions.
5. Decide whether the rank-one characterization of maximal purity warrants a focused theorem issue.
6. Add continuous-outcome measurement theory only after a measure-theoretic API is designed.
