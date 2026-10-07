---
status: accepted
---

# Assign modules by semantic responsibility

Place reusable results in the earliest layer whose semantic concepts determine them, and state them in those terms rather than in a consumer's coordinates. Generic mathematics and quantum-state/response foundations remain upstream; Common owns statistics-independent constructions, with Fermionic and Bosonic realizations downstream.

Treat module boundaries as semantic contracts, not proof stages: keep independently meaningful laws and public endpoints with their owners, while one-use proof routes and aliases remain private or inline. Keep an umbrella only when it names a coherent package or groups related leaves; remove a single-child forwarder and have consumers import the canonical owner.

Use explicit downstream adapters at representation boundaries. This trades adapter code for acyclic dependencies, narrower imports, and shared semantic laws.

Evidence: [layer graph](../../scripts/architecture/second_quantization.json), [second-quantization architecture](../architecture/second-quantization.md), [intrinsic balance laws](../../LeanCondensedMatter/Analysis/ConservationLaw/IntrinsicBalanceLaw.lean), [current representations](../../LeanCondensedMatter/Analysis/ConservationLaw/CurrentRepresentation.lean), [Heisenberg evolution](../../LeanCondensedMatter/QuantumTheory/ConservationLaw/HeisenbergEvolution.lean), [Fermionic `dΓ` bridge](../../LeanCondensedMatter/SecondQuantization/Fermionic/Field/GeneralizedQuantity.lean), [Quartic diagram umbrella](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/Quartic.lean), [TwoPoint diagram umbrella](../../LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/TwoPoint.lean), [Fermionic TwoPoint expansion umbrella](../../LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion.lean), [exchange-weighted pairing bridge](../../LeanCondensedMatter/Permutation/PairingBridge.lean), [generic first-pair recurrence](../../LeanCondensedMatter/Combinatorics/PerfectPairing/FirstPairRecursion.lean), and [conventions](../conventions.md).

## Historical evidence

Issues [#2526](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2526), [#2382](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2382), and [#2489](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2489) apply the ownership rule to finite traces and conservation-law adapters; [PR #2730](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2730) applies it to package routing. [PR #2808](https://github.com/naoki-cpp/LeanCondensedMatter/pull/2808) applies the same rule to the single-child Fredholm forwarder; its determinant-domain decision is recorded in ADR 0014. The full issue-by-issue review and skipped-PR ranges are in [history-review.md](history-review.md).
