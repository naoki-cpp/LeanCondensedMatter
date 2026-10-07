---
status: accepted
---

# Use one density-state model across dimensions

Use `QuantumTheory.DensityOperator` as the canonical mixed-state type: a positive bounded operator with general trace-class membership and canonical complex trace one. Define physical pure states as the subtype of density operators represented by normalized vectors, while retaining `StateVector` for computations with representatives.

Equality of physical pure states is then equality of density operators; unit-modulus global phase does not create a different state. This reuses the mixed-state expectation and dynamics infrastructure instead of introducing a separate ray quotient and parallel pure-state theory.

Keep the state type dimension-independent and introduce finite-dimensional assumptions only at results that need them. The current spectral model is not an arbitrary non-self-adjoint trace-class or unbounded-observable theory; those extensions require their own analytic foundations. Finite matrix formulas specialize the same state type.

Evidence: [density-state definition](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Basic.lean), [pure states and phase equivalence](../../LeanCondensedMatter/QuantumTheory/DensityOperator/PureState.lean), and [density architecture](../architecture/quantum-density-theory.md).

## Historical evidence

[Issue #580](https://github.com/naoki-cpp/LeanCondensedMatter/issues/580) completes dimension-independent bounded dynamics for vector representatives and canonical density states: Schrödinger/Heisenberg picture equivalence, unitary density conjugation, bounded equations of motion, and conserved expectations. This extends the existing state APIs without making unbounded operators into observables. A projective quotient remains unnecessary; phase-invariant rank-one states and representative-level calculations are both available.

[Issue #556](https://github.com/naoki-cpp/LeanCondensedMatter/issues/556) formalizes the distinction between normalized `StateVector` representatives and physical `PureState` values. Store the latter as rank-one density operators so phase-related vectors are identified by ordinary density equality; retain vector representatives for calculations. The intrinsic criterion `purity ρ = 1` is equivalent to the existing rank-one predicate, so a projective-space quotient or separate range API is unnecessary without a concrete consumer.

[Issue #483](https://github.com/naoki-cpp/LeanCondensedMatter/issues/483) makes the dimension-independent `DensityOperator` the sole mixed-state model and organizes expectation, countable POVM, `ENNReal` entropy, Gibbs, and finite-dimensional results by responsibility. Finite matrix facts are bridges on the canonical state type, not a second state architecture. All consumers were migrated and repository audits prohibit duplicate state/POVM declarations and obsolete compatibility aliases.

[Issue #477](https://github.com/naoki-cpp/LeanCondensedMatter/issues/477) derives finite free-fermion entropy from the canonical `freeGibbsDensityOperator` through the existing diagonal density-entropy and finite trace bridges. Factoring the occupation sum yields independent one-mode binary entropies, with the `0 * log 0` boundary handled by the shared scalar convention. This specialization adds physics-facing theorems without reviving a separate weighted Gibbs-functional state model.

[Issue #438](https://github.com/naoki-cpp/LeanCondensedMatter/issues/438) completes bounded-Hamiltonian Gibbs variational theory with attainment and an equality-if-and-only-if uniqueness theorem under explicit compactness, spectral summability, temperature, and partition-function hypotheses. The equality proof follows the existing inequality chain's saturation cases and reconstructs the density operator from the resulting spanning eigenfamily. The compact Gibbs operator still forces finite dimensionality, so this does not enlarge the model into unbounded infinite-dimensional thermodynamics.

[Issue #437](https://github.com/naoki-cpp/LeanCondensedMatter/issues/437) completes purity directly on the dimension-independent density-operator type as the sum of squared spectral eigenvalues. Positivity, the upper bound one, rank-one purity, and the converse characterization `purity = 1` all use the canonical state model; finite-dimensionality appears only in the bridge to the ordinary matrix trace `Tr(ρ²)`. This avoids a parallel purity type and makes the purity-one characterization part of the canonical API.

[PR #1](https://github.com/naoki-cpp/LeanCondensedMatter/pull/1) introduced normalized vector representatives, self-adjoint observables, density operators, and discrete Born probabilities together. It explicitly distinguished defining an observable by self-adjointness from adopting the state-space and measurement postulates. That distinction remains important: a definition fixes the mathematical object, while the Born rule supplies its physical interpretation.

The initial density and measurement construction was finite-dimensional because trace-class infrastructure was unavailable. This is evidence for keeping analytic scope explicit, not a reason to reintroduce that restriction into the present spectral density model. The PR's term “purification” referred to the rank-one embedding of an already pure vector state; it does not establish purification of an arbitrary mixed state on a larger Hilbert space.

[PR #4](https://github.com/naoki-cpp/LeanCondensedMatter/pull/4) made the canonical-distribution claim precise as Helmholtz free-energy minimization at positive inverse temperature, rather than loosely calling it entropy maximization at fixed energy. It also used separate energy and density eigenbases: a competing state need not commute with the Hamiltonian. Current [Gibbs variational results](../../LeanCondensedMatter/QuantumTheory/Gibbs/Variational.lean) and [minimizer uniqueness](../../LeanCondensedMatter/QuantumTheory/Gibbs/MinimizerUniqueness.lean) should retain their explicit hypotheses instead of treating the thermodynamic interpretation as an additional axiom.

[PR #6](https://github.com/naoki-cpp/LeanCondensedMatter/pull/6) separately established that the constructed Gibbs state attains the bound. Its finite spectral argument compared eigenvalues as multisets rather than imposing an ordering correspondence between two eigenbases. The lasting semantic distinction is between a universal lower bound, attainment by a constructed state, and uniqueness of the minimizer: one statement must not be used as shorthand for all three. The particular characteristic-polynomial proof is not a required implementation strategy.

[Issue #373](https://github.com/naoki-cpp/LeanCondensedMatter/issues/373) likewise separates a measurement's finite outcome sum from finite Hilbert-space dimension: a POVM with finitely many effects needs no dimension hypothesis merely to state positivity and sum-to-identity. Ordinary matrix-trace specializations still require their own finite-dimensional boundary. Assumptions should follow the operations in the declaration, not the first implementation that consumed it.

[Issue #376](https://github.com/naoki-cpp/LeanCondensedMatter/issues/376) records a sharp limitation of the bounded Gibbs model: `exp(-βH)` is invertible for bounded self-adjoint `H`, so if this Gibbs operator is also compact then the identity is compact and the Hilbert space must be finite-dimensional. Theorems about the operator function may be dimension-independent, but this particular compact normalized Gibbs-state construction is not an infinite-dimensional thermal theory. Such states require an unbounded Hamiltonian architecture.

That extension has a concrete spectral route in [ADR 0013](0013-diagonal-heat-operator.md): build the trace-class heat operator from summable weights on an energy basis, without storing the unbounded Hamiltonian in the bounded-observable state model.

[Issue #407](https://github.com/naoki-cpp/LeanCondensedMatter/issues/407) motivates reusable Hilbert-basis formulas for density-state weights, normalization, entropy, and energy. Gibbs proofs should consume these generic state-level results instead of rebuilding normalization and diagonal entropy arguments locally. This keeps the state model canonical while allowing the diagonal heat-operator backend to reuse it.

[Issue #412](https://github.com/naoki-cpp/LeanCondensedMatter/issues/412) connected the finite-dimensional density API to the same spectral-trace/diagonal entropy route. This replaced characteristic-polynomial root matching between independently enumerated eigenvalue lists with a basis-level bridge, while preserving the public entropy theorem. Finite-dimensionality remains where ordinary matrix trace is used; it does not require a second entropy model.

The spectral foundation avoids ambient separability assumptions by working on the nonzero spectral support; see [ADR 0012](0012-nonzero-spectral-support.md) for that independent operator-theory decision.
