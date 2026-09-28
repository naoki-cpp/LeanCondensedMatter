---
status: accepted
---

# Separate diagram combinatorics, physical amplitudes, and convergence

Put finite partitions, pairings, and generic connected-decomposition mathematics in Combinatorics. Common diagrammatics owns many-body diagram structure, component restriction and reassembly, and ordering; statistics-specific layers supply pair values, signs, and physical amplitudes.

This allows shared component arguments without importing fermionic thermal semantics into generic combinatorics. Ordering is mathematical data when crossing parity matters, so reindexing must preserve or explicitly transport that information rather than use an arbitrary finite-type equivalence.

Keep formal power-series identities separate from analytic statements about convergent expansions. A formal linked-cluster identity does not authorize evaluation of its series at a physical parameter. Analytic endpoints add the required finite-dimensional, integrability, or convergence hypotheses. The two-point expansion's Semantics → Factorization → Analysis → Integration → Series layering makes these responsibilities explicit.

Evidence: [connected-decomposition mathematics](../../LeanCondensedMatter/Combinatorics/Cumulant/ConnectedDecomposition.lean), [diagrammatics architecture](../../notes/architecture/second-quantization.md), [layer graph](../../scripts/architecture/second_quantization.json), and [analytic linked-cluster endpoint](../../LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/Analytic.lean).
