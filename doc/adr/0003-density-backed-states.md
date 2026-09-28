---
status: accepted
---

# Use one density-state model across dimensions

Use `QuantumTheory.DensityOperator` as the canonical mixed-state type: a positive bounded operator with a spectral trace-class witness and trace one. Define physical pure states as the subtype of density operators represented by normalized vectors, while retaining `StateVector` for computations with representatives.

Equality of physical pure states is then equality of density operators; unit-modulus global phase does not create a different state. This reuses the mixed-state expectation and dynamics infrastructure instead of introducing a separate ray quotient and parallel pure-state theory.

Keep the state type dimension-independent and introduce finite-dimensional assumptions only at results that need them. The current spectral model is not an arbitrary non-self-adjoint trace-class or unbounded-observable theory; those extensions require their own analytic foundations. Finite matrix formulas specialize the same state type.

Evidence: [density-state definition](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Basic.lean), [pure states and phase equivalence](../../LeanCondensedMatter/QuantumTheory/DensityOperator/PureState.lean), and [density architecture](../../notes/architecture/quantum-density-theory.md).
