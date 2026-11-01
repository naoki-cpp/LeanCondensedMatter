---
status: accepted
---

# Define bounded operator functions through functional calculus

Use Mathlib's continuous functional calculus to construct functions of bounded self-adjoint operators. Eigenbasis formulas are evaluation theorems for these constructions rather than the sole means of defining them. This avoids building finite-dimensional enumeration into generic operator semantics and places reusable operator arguments in Analysis, upstream of the quantum-state consumers.

The trade-off is that consumers must meet functional-calculus hypotheses and prove bridges to their chosen spectral coordinates. Functional calculus alone does not establish trace-classness, summability, or a Gibbs normalization, and a bounded-Hamiltonian construction does not supply an unbounded-Hamiltonian theory.

Evidence: the current [Gibbs operator](../../LeanCondensedMatter/QuantumTheory/Gibbs/State.lean) and [entropy operator](../../LeanCondensedMatter/QuantumTheory/Entropy/Basic.lean).

Applying a scalar function can merge eigenspaces or send nonzero eigenvalues to zero. Do not
identify the transformed operator's spectral index with the input index without a bridge.
Compactness, transformed-eigenvalue summability, and trace formulas require their own proofs.
For a bounded Hamiltonian, compactness of the invertible Gibbs exponential forces finite
dimension; continuous functional calculus alone does not remove that obstruction.
