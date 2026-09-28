---
status: accepted
---

# Separate thermal states from the pairing recursion

For bounded observables, use the canonical density-operator expectation; finite trace ratios and occupation-coordinate sums are representations connected to it by explicit bridges. A normalized functional with arbitrary complex weights has no automatic Gibbs-state interpretation.

Prove the finite-temperature Bloch–de Dominicis expansion through `ExpectationPairingRecursion`, which accepts an ordered expectation, pair values, admissibility, empty-product normalization, and a first-pair recurrence. Representation-specific implementations supply the KMS/exchange and analytic arguments.

This avoids rebuilding the pairing induction for each representation and keeps finite-dimensional assumptions out of the generic theorem. Its cost is an explicit admissibility contract: the generic expansion cannot discharge summability, operator-domain, or KMS obligations. Unbounded observables need a separate integrability-aware expectation rather than being passed to the bounded density-state API.

Evidence: [recursion contract and theorem](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean), [finite Gibbs bridge](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/FiniteGibbsExpectationBridge.lean), and [thermal architecture](../../notes/roadmaps/thermal-expectation-architecture.md).
