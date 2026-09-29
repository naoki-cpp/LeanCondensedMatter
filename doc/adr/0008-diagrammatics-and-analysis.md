---
status: accepted
---

# Separate diagram combinatorics, physical amplitudes, and convergence

Put finite pairings, partitions, ordering, and component decomposition in generic combinatorics; Common diagrammatics owns statistics-independent diagram structure, while statistics-specific layers supply signs, fields, and physical amplitudes. Keep generic analytic obligations such as measurability, integrability, and finite-family factorization separate from formal identities.

Ordering and reindexing are semantic data whenever they determine crossing signs or component order, so consumers supply the relevant order and embeddings explicitly. Reusable theorem statements belong with the earliest owner of their meaning; one-use proof stages and model-specific transports remain local.

Combinatorial factorization alone establishes neither a physical amplitude nor convergence, evaluation, or a higher-point linked-cluster theorem. Those require separate consumer bridges and hypotheses.

Evidence: [connected-decomposition mathematics](../../LeanCondensedMatter/Combinatorics/Cumulant/ConnectedDecomposition.lean), [generic external-insertion diagrams](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ExternalInsertion/Core/Diagram.lean), [two-point diagrams](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/TwoPoint/Core/Diagram.lean), [diagrammatics architecture](../../notes/architecture/second-quantization.md), [layer graph](../../scripts/architecture/second_quantization.json), and [analytic linked-cluster endpoint](../../LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/Analytic.lean).

## Historical evidence

Issue [#815](https://github.com/naoki-cpp/LeanCondensedMatter/issues/815) consolidates proof staging while preserving semantic endpoints; issue [#1267](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1267) keeps higher-point external insertions distinct from the mature two-point structure. Issues [#2431](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2431) and [#2435](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2435) place formal source normalization and connected-expansion algebra upstream of physical amplitudes and analytic convergence. Sequential issue dispositions and PR gaps are tracked in [history-review.md](history-review.md).
