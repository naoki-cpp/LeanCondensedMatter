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

## Bounded one-particle dynamics

Status: `in progress` under #580; unitary propagation, picture equivalence, and the bounded
Schrödinger, Heisenberg, and von Neumann equations are proved.

`QuantumTheory/LinearResponse/FreeDynamics.lean` defines the bounded free system and propagator

```lean
U₀(t) = exp (-(i t / ℏ) H₀)
```

for a bounded self-adjoint Hamiltonian and `ℏ > 0`. The pure-state dynamics layer proves:

- the two unitary identities `U₀(t)† U₀(t) = 1` and `U₀(t) U₀(t)† = 1`;
- `freePropagatorUnitary`, bundling `U₀(t)` as a unitary element;
- norm preservation `‖U₀(t) x‖ = ‖x‖` on an arbitrary complete complex Hilbert space;
- normalized Schrödinger-picture evolution `evolveState system ψ t : State H`;
- identity, additive-time action, and positive/negative-time inverse laws;
- exact compatibility of evolution with unit-modulus global-phase representatives through
  `phaseState`, without introducing a ray quotient.

`QuantumTheory/LinearResponse/PictureEquivalence.lean` adds:

- `heisenbergObservable`, bundling the Heisenberg evolution of a self-adjoint observable;
- exact complex and lossless real pure-state expectation identities between Schrödinger and
  Heisenberg pictures;
- `evolveDensityOperator system ρ t = U₀(t) ρ U₀(t)†` as a canonical density operator;
- preservation of positivity, compact spectral trace-class data, and spectral trace one;
- unitary transport of Hilbert bases;
- exact complex density-state picture equivalence for every bounded operator;
- the corresponding lossless real identity for observables.

`Analysis/Operator/TraceClass/Unitary.lean` owns the reusable analytic boundary: unitary conjugation
preserves eigenspaces up to linear equivalence, eigenspace multiplicities, spectral summability,
compactness, positivity, spectral trace class, and spectral trace. The density-state expectation
proof remains dimension-independent by diagonalizing the original state, transporting its Hilbert
basis, and comparing the two absolutely convergent diagonal series.

`QuantumTheory/LinearResponse/EquationsOfMotion.lean` supplies norm derivatives throughout the
bounded theory:

- operator-norm differentiability of `freePropagator system t` and its negative-time form;
- the generator relation and explicit bounded Schrödinger equation
  `dψ/dt = -(i/ℏ) H₀ ψ` for state-vector representatives;
- the generator relation and explicit bounded Heisenberg equation
  `dA_H/dt = (i/ℏ) (H₀ A_H - A_H H₀)`;
- the generator relation and explicit bounded von Neumann equation
  `dρ/dt = -(i/ℏ) (H₀ ρ - ρ H₀)`;
- dimension-independent proofs based only on Banach-algebra exponential differentiation,
  continuous-linear evaluation, product rules, and the generator–propagator commutation law.

The remaining #580 package is conservation laws and downstream reuse of these canonical dynamics
APIs.

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
- existence of a Hilbert basis diagonalizing every density operator, extending the canonical
  nonzero spectral eigenvector family by kernel vectors of weight zero;
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

1. Complete #580 with conservation of Hamiltonian and commuting-observable expectations, then reuse
   the canonical dynamics APIs in linear response where they remove duplicate picture changes.
2. Prove uniqueness of the Gibbs free-energy minimizer.
3. Design an unbounded Hamiltonian interface supporting genuine infinite-dimensional Gibbs states.
4. Connect the canonical density-state expectation to completed Fock-space and KMS constructions.
5. Decide whether the rank-one characterization of maximal purity warrants a focused theorem issue.
6. Add continuous-outcome measurement theory only after a measure-theoretic API is designed.
