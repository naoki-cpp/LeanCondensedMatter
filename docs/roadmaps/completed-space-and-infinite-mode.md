# Completed-space and infinite-mode boundary

Completion, unbounded-operator domains, thermal summability, and thermodynamic limits are separate
analytic problems. This note records the current completed fermionic and free-bosonic thermal
boundaries and what remains open.

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

Uniformly bounded coordinatewise scalar multiplication uses Mathlib `lp.mapCLM`, specialized locally
to completed-space diagonal operators.
For a diagonal algebraic Fock operator, a continuous extension to the completed space exists
**if and only if its complex diagonal weights are uniformly bounded**. The general theorem
`exists_bounded_diagonal_extension_iff` needs no `Finite` or `Fintype` hypothesis;
`completedBoundedDiagonalOperator_comp_algebraicToCompleted` identifies the extension on
the dense algebraic core. This criterion does not extend arbitrary algebraic endomorphisms
without an operator-norm bound. Genuinely unbounded diagonal weights, such as particle-number
and free-Hamiltonian energies, keep explicit `LinearPMap` domains; completion alone never
licenses coercing an unbounded Hamiltonian or number operator to a
bounded map.

## Thermal boundary

Completed thermal specializations live under `SecondQuantization.Fermionic.Thermal.Completed`.
The full-Fock grand-canonical state uses `Common.grandCanonicalGibbsDensityOperator` with explicit
chemical potential `μ`, whose normalization reuses `QuantumTheory.Gibbs.Eigenbasis`.

The completed free-fermion route includes:

- grand-canonical pure-point Gibbs states with explicit `μ` and occupation-weight summability;
- occupation-basis formulas for bounded expectations and an explicit integrability domain for the
  completed total-number expectation;
- generic unbounded energy expectation through `QuantumTheory.Gibbs.EigenbasisExpectation`;
- a one-particle sufficient condition for free-fermion Gibbs summability and the corresponding
  partition-product identity;
- bounded thermal ladder packaging, Gibbs intertwining and KMS rotation with factors
  `exp(±β(εᵢ - μ))`, CAR peel, and the completed Bloch--de Dominicis recursion;
- finite-mode Gibbs truncations at explicit `μ` and convergence of bounded-observable expectations
  to the completed grand-canonical Gibbs expectation.

The last item is weak convergence against bounded observables, not a thermodynamic limit or a general
trace-norm convergence theorem. For finite fermionic mode sets, the completed grand-canonical density
is intertwined with the finite Gibbs density under `Common.completedFiniteHilbertEquiv`;
the finite density expectation is the `Common.summableDiagonalTraceRatioLinear` of #4074.
This finite bridge does not extend to a trace-ratio identification for arbitrary completed operators.

## Completed bosonic free thermal representation

`SecondQuantization.Bosonic.CompletedFockSpace Mode := ℓ²(Bosonic.Occupation Mode, ℂ)` specializes
the same Common completed occupation-space infrastructure. The free heat operator
`exp (-βH₀)` is bounded for arbitrary mode types with nonnegative one-particle energies.
For arbitrary `Mode`, an explicit `EigenbasisGibbsSummable (freeEigenvalue ε) β` hypothesis
supplies:

- trace-classness of the physical completed free heat operator `exp(-βH)`;
- equality of its trace with the explicit grand-canonical partition function at `μ = 0`;
- normalization to `Common.grandCanonicalGibbsDensityOperator ε β 0`. General `μ`
  is supplied directly by the Common API, not a bosonic zero-μ constructor.

For finite `Mode`, the geometric-series theorem `eigenbasisGibbsSummable_freeEigenvalue`
supplies occupation summability under positive mode energies. For arbitrary `Mode`, the theorem
`eigenbasisGibbsSummable_freeEigenvalue_of_mode` derives the same conclusion from strict
positive mode gaps and the one-particle `EigenbasisGibbsSummable ε β` condition. It uses
`Finsupp.graph` and Mathlib's summability of finite-subset products, without finiteness or
countability typeclass assumptions on `Mode`. The infinite partition-product identity has
not yet been formalized.

This does not make bosonic creation, annihilation, number, or interacting Hamiltonians bounded.
The single-mode number operator and free Hamiltonian are now represented separately as maximal
diagonal `LinearPMap` operators on their natural weighted `ℓ²` domains. Their finite-support
algebraic core agrees with the existing algebraic operators, and the real diagonal weights make both
operators self-adjoint through the Common diagonal analytic theory. Creation and annihilation are
represented as maximal weighted-shift `LinearPMap` operators on the natural square-root occupation
domains, are densely defined and closed, and are mutual adjoints. They agree with the algebraic
ladder operators on the finite-support core. For each mode, both mixed products have maximal domain
`Dom(Nᵢ)` and satisfy `aᵢ† aᵢ = Nᵢ`, `aᵢ aᵢ† = Nᵢ + 1`, and the equal-mode completed CCR there.
An ordered number-conserving quartic vertex is also defined as the exact domain-aware composition
`a† a† a a` of four completed ladder `LinearPMap` operators. A finite family of such vertices now
has the canonical common intersection domain, which contains the algebraic finite-support core and
is therefore dense. The corresponding finite completed quartic interaction is a `LinearPMap` sum on
that domain and agrees there on the algebraic core with `Common.quarticInteractionOn`. These exact
domains have not yet been replaced by closed-form weighted `ℓ²` descriptions.

## Finite-mode fermionic compatibility

For finite fermionic `Mode`, the completed occupation space is finite dimensional and is canonically related to
the finite Hilbert Fock realization through `SecondQuantization.Common.CompletedSpace` compatibility
results. The same generic pure-point Gibbs probabilities are used on both representations; no
independent finite Gibbs state model is required.

For arbitrary `Mode`, finite-mode projections indexed by `Finset Mode` are contractions, eventually
fix algebraic vectors, and converge strongly to the identity. No countability assumption on `Mode` is
needed for that representation-level statement.

## Stationary completed Gibbs states

`Common.Thermal.CompletedResponse` connects the existing summable grand-canonical density
to the unitary-group linear-response interface: it is stationary under Stone evolution of any
real diagonal energy function on the same occupation basis. The statement applies to both
statistics without a finite-mode hypothesis. Physical Hamiltonian energies divided by ℏ may be
used independently of the thermal generator `E - μ N`. The observable remains bounded; this
does not supply response theory for unbounded currents or an infinite-volume equilibrium state.

The analysis input is `LinearPMap.stoneEvolution_eigenvector`: a domain eigenvector of real
energy `E` evolves by the phase `exp(-i t E)`. It follows from the existing strong Stone derivative,
Mathlib's exponential derivative, and derivative-zero constancy using an integrating factor.
Eigenvector expectation invariance now follows from cancellation of this phase with its conjugate.
For completed diagonal generators, `completedDiagonalOperator_basisState` supplies the eigenvector
hypothesis directly. This identifies occupation-basis time evolution without a finite-mode
assumption; it does not construct the Fock lift of a general unitary mixing one-particle modes.

`Common.Thermal.CompletedResponse` supplies positive-switching-rate integrability of the existing
adiabatic scalar kernel for this completed Gibbs density under real diagonal Stone dynamics.
`DensityOperator.continuous_expectation_of_diagonal` uses continuous diagonal matrix coefficients
and a uniform operator bound, with the density weights providing a summable majorant through
Mathlib's `continuous_tsum`. `Response.DensitySusceptibility` applies that fact to the scalar
commutator using strong continuity of the unitary group. It does not require operator-norm
continuity of observable orbits, and does not extend this conclusion to arbitrary normalized
functionals. The causal extension is measurable and the existing exponential-damping theorem
then gives integrability for every positive switching rate. The zero-rate limit remains separate.

## Open work

- identify the arbitrary-mode free-boson partition sum with the convergent infinite product
  of one-mode geometric partition functions;

- explicit weighted-domain characterizations and identities for mixed-mode and quartic bosonic
  ladder products;
- completed interacting-Hamiltonian domain/control beyond the finite quartic interaction itself;
- interacting completed-space Dyson theory with all required product domains;
- stronger convergence topologies for Gibbs truncations when justified;
- infinite-volume or thermodynamic limits with an explicit directed system, observable algebra,
  state topology, and uniform estimates.
