---
status: accepted
---

# Construct discrete heat operators from summable spectral weights

For a discrete unbounded-Hamiltonian thermal model, construct the bounded heat operator from an energy Hilbert basis and absolutely summable Boltzmann weights, then normalize that positive trace-class operator into a density state. Do not represent an unbounded Hamiltonian itself as the bounded `Observable` type merely to reuse the bounded Gibbs API.

The diagonal-series construction gives a compact operator, explicit basis action, positivity, and a spectral-trace formula under stated summability and nonzero-partition hypotheses. It is a thermal-state backend, not yet a complete unbounded Hamiltonian/domain theory; integrability, time evolution, and unbounded observables retain their own analytic obligations.

Evidence: [diagonal operator construction](../../LeanCondensedMatter/Analysis/Operator/Diagonal.lean), [spectral-trace packaging](../../LeanCondensedMatter/Analysis/Operator/TraceClass/DiagonalSpectralTrace.lean), and [density normalization](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Normalize.lean).

## Historical evidence

[Issue #438](https://github.com/naoki-cpp/LeanCondensedMatter/issues/438) completes Gibbs-state entropy, free-energy attainment, and uniqueness for the bounded-Hamiltonian API under explicit compactness and spectral hypotheses, while recording that compactness forces finite dimension. This confirms the scope boundary: the diagonal heat-operator construction is the route to discrete infinite-dimensional density states, but neither it nor bounded Gibbs variational theorems establish the unbounded dynamics and domain theory.

[Issue #393](https://github.com/naoki-cpp/LeanCondensedMatter/issues/393) motivates this route from the compactness obstruction for bounded Gibbs Hamiltonians. An energy basis with summable positive weights constructs the heat operator directly as `Σᵢ aᵢ |eᵢ⟩⟨eᵢ|`. This yields genuine infinite-dimensional density states when the total weight is positive, without asserting that the underlying energy operator is bounded.
