---
status: accepted
---

# Define bounded operator functions through functional calculus

Use Mathlib's continuous functional calculus to construct functions of bounded self-adjoint operators. Eigenbasis formulas are evaluation theorems for these constructions rather than the sole means of defining them. This avoids building finite-dimensional enumeration into generic operator semantics and places reusable operator arguments in Analysis, upstream of the quantum-state consumers.

The trade-off is that consumers must meet functional-calculus hypotheses and prove bridges to their chosen spectral coordinates. Functional calculus alone does not establish trace-classness, summability, or a Gibbs normalization, and a bounded-Hamiltonian construction does not supply an unbounded-Hamiltonian theory.

Evidence: the current [Gibbs operator](../../LeanCondensedMatter/QuantumTheory/Gibbs/State.lean) and [entropy operator](../../LeanCondensedMatter/QuantumTheory/Entropy/Basic.lean).

## Historical evidence

[Issue #376](https://github.com/naoki-cpp/LeanCondensedMatter/issues/376) expanded the role of continuous functional calculus: Gibbs and entropy operators can act on eigenvectors without finite-dimensional spectral-list arguments. However, applying `f` can merge eigenspaces or send nonzero eigenvalues to zero, so the transformed operator's spectral index cannot simply reuse the input index; compactness, transformed-eigenvalue summability, and trace equality need explicit bridges. The entropy API stays `ENNReal`-valued when entropy may diverge. For the bounded-Hamiltonian Gibbs construction, compactness of the invertible exponential forces finite-dimensionality, so CFC generality alone does not produce an infinite-dimensional Gibbs state.

[PR #7](https://github.com/naoki-cpp/LeanCondensedMatter/pull/7) explicitly motivated functional calculus as the replacement for finite eigenbasis-sum constructions when generalizing operator theory. It supplied only the polynomial eigenvector step and recorded the continuous-function bridge as a target. This source establishes the architectural motivation, not completion of the full bridge at that point.
