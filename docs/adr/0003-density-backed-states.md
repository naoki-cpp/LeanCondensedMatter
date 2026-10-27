---
status: accepted
---

# Use one density-state model across dimensions

Use `QuantumTheory.DensityOperator` as the canonical mixed-state type: a positive bounded operator with general trace-class membership and canonical complex trace one. Define physical pure states as the subtype of density operators represented by normalized vectors, while retaining `StateVector` for computations with representatives.

Equality of physical pure states is then equality of density operators; unit-modulus global phase does not create a different state. This reuses the mixed-state expectation and dynamics infrastructure instead of introducing a separate ray quotient and parallel pure-state theory.

Keep the state type dimension-independent and introduce finite-dimensional assumptions only at results that need them. The density-state model describes positive trace-class states and expectations of bounded operators. Unbounded-observable expectations require separate domain and integrability arguments. Finite matrix formulas specialize the same state type.

Evidence: [density-state definition](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Basic.lean), [pure states and phase equivalence](../../LeanCondensedMatter/QuantumTheory/DensityOperator/PureState.lean), and [density architecture](../architecture/quantum-density-theory.md).

## Analytic and physical boundaries

General trace-class membership and positivity imply the spectral properties used by the state
API; the density structure does not store a separate spectral bundle. The nonzero-support
construction avoids an ambient separability assumption; see
[ADR 0012](0012-nonzero-spectral-support.md).

Normalized vector representatives embed as rank-one density states. This does not assert
purification of an arbitrary mixed state on a larger Hilbert space. Likewise, defining a
self-adjoint observable does not supply the Born measurement postulate.

Gibbs lower bounds, attainment by the Gibbs state, and uniqueness of the minimizer are distinct
results with explicit hypotheses; see the [variational theorem](../../LeanCondensedMatter/QuantumTheory/Gibbs/Variational.lean)
and [minimizer uniqueness](../../LeanCondensedMatter/QuantumTheory/Gibbs/MinimizerUniqueness.lean).
Do not require a competing density state to commute with the Hamiltonian merely to compare
their free energies.

Summable heat weights provide the state-construction boundary for unbounded energy spectra;
see [ADR 0013](0013-diagonal-heat-operator.md). The unbounded Hamiltonian is not itself a
bounded observable. Finite matrix traces and finite outcome sums impose different finiteness
requirements and do not justify restricting the canonical state type to finite dimension.
