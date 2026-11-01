---
status: accepted
---

# Separate diagram combinatorics, physical amplitudes, and convergence

Put finite pairings, partitions, ordering, and component decomposition in generic combinatorics; Common diagrammatics owns statistics-independent diagram structure, while statistics-specific layers supply signs, fields, and physical amplitudes. Keep generic analytic obligations such as measurability, integrability, and finite-family factorization separate from formal identities.

Ordering and reindexing are semantic data whenever they determine crossing signs or component order, so consumers supply the relevant order and embeddings explicitly. Reusable theorem statements belong with the earliest owner of their meaning; one-use proof stages and model-specific transports remain local.

Combinatorial factorization alone establishes neither a physical amplitude nor convergence, evaluation, or a higher-point linked-cluster theorem. Those require separate consumer bridges and hypotheses. Permutation connected-cycle algebra is statistics-independent, while grand-partition constructions and the analytic obligations of Bose/Fermi occupation spaces belong in second quantization. Formal identities imply neither evaluation at `t = 1` nor convergence; bosonic convergence and fermionic finite-mode partition formulas remain statistics-specific endpoints.

Keep arbitrary-external-insertion diagrams separate from the mature two-point representation.
Shared combinatorics does not justify changing their definitional normal forms; introduce a
representation bridge only for a concrete consumer.

Evidence: [connected-decomposition mathematics](../../LeanCondensedMatter/Combinatorics/Cumulant/ConnectedDecomposition.lean), [generic external-insertion diagrams](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ExternalInsertion/Core/Diagram.lean), [two-point diagrams](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/TwoPoint/Core/Diagram.lean), [diagrammatics architecture](../architecture/second-quantization.md), [layer graph](../../scripts/architecture/second_quantization.json), and [analytic linked-cluster endpoint](../../LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/Analytic.lean).
