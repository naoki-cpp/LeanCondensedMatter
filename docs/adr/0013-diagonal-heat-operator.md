---
status: accepted
---

# Construct discrete heat operators from summable spectral weights

For a discrete unbounded-Hamiltonian thermal model, construct the bounded heat operator from an energy Hilbert basis and absolutely summable Boltzmann weights, then normalize that positive trace-class operator into a density state. Do not represent an unbounded Hamiltonian itself as the bounded `Observable` type merely to reuse the bounded Gibbs API.

The diagonal-series construction gives a positive compact operator with explicit basis action, general trace-class membership, and trace formulas under stated summability hypotheses. Normalization additionally requires a nonzero partition function. This construction supplies thermal states; integrability, time evolution, and unbounded observables retain their own analytic obligations.

Evidence: [diagonal operator construction](../../LeanCondensedMatter/Analysis/Operator/Diagonal.lean), [general trace-class diagonal operators](../../LeanCondensedMatter/Analysis/Operator/TraceClass/Diagonal.lean), [spectral specialization](../../LeanCondensedMatter/Analysis/Operator/TraceClass/Spectral/Diagonal.lean), and [density normalization](../../LeanCondensedMatter/QuantumTheory/DensityOperator/Normalize.lean).
