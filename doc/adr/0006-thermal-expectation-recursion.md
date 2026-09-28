---
status: accepted
---

# Separate thermal states from the pairing recursion

For bounded observables, use the canonical density-operator expectation; finite trace ratios and occupation-coordinate sums are representations connected to it by explicit bridges. A normalized functional with arbitrary complex weights has no automatic Gibbs-state interpretation.

Prove the finite-temperature Bloch–de Dominicis expansion through `ExpectationPairingRecursion`, which accepts an ordered expectation, pair values, admissibility, empty-product normalization, and a first-pair recurrence. Representation-specific implementations supply the KMS/exchange and analytic arguments.

This avoids rebuilding the pairing induction for each representation and keeps finite-dimensional assumptions out of the generic theorem. Its cost is an explicit admissibility contract: the generic expansion cannot discharge summability, operator-domain, or KMS obligations. Unbounded observables need a separate integrability-aware expectation rather than being passed to the bounded density-state API.

Evidence: [recursion contract and theorem](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean), [finite Gibbs bridge](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/FiniteGibbsExpectationBridge.lean), [canonical pure-point Gibbs states](../../LeanCondensedMatter/QuantumTheory/Gibbs/PurePoint.lean), [completed representation umbrella](../../LeanCondensedMatter/SecondQuantization/Fermionic/CompletedSpace.lean), [fermionic thermal umbrella](../../LeanCondensedMatter/SecondQuantization/Fermionic/Thermal.lean), and [thermal architecture](../../notes/roadmaps/thermal-expectation-architecture.md).

## Historical evidence

[Issue #1555](https://github.com/naoki-cpp/LeanCondensedMatter/issues/1555) separated representation from thermal semantics: `Fermionic.CompletedSpace` owns basis/core, operators, domains, finite compatibility, and representation-truncation convergence; `Fermionic.Thermal` owns completed Gibbs/KMS/ladder/recursion and Gibbs-expectation convergence. Generic normalized Gibbs-state mathematics continues to use the single `QuantumTheory.Gibbs.PurePoint` owner. State-independent finite-Hilbert adjoint/trace infrastructure moved below `Common.Thermal` when direct nonthermal consumers justified it. Finite and completed specializations remain separate where their representations differ; no representation typeclass or duplicate Common Gibbs layer was introduced for symmetry.

[Issue #440](https://github.com/naoki-cpp/LeanCondensedMatter/issues/440) supplies the generic pairing contract from #421 with a completed fermionic instance using the bounded trace-class Gibbs density and bounded ladder operators. KMS rotation is proved by occupation-basis reindexing, so this consumer needs no formal product API for an unbounded Hamiltonian. Add domain-product lemmas only when a later expression actually consumes them; the generic recursion remains independent of occupation bases and finite-mode assumptions.

[Issue #435](https://github.com/naoki-cpp/LeanCondensedMatter/issues/435) instantiates the generic contract for bosons only after supplying a convergence-aware free-Gibbs domain, KMS rotation, and the product-closure or integrability facts used by each Dyson order. The generic pairing theorem remains independent of configurations and finite enumeration; the bosonic backend owns its analytic obligations.

[Issue #421](https://github.com/naoki-cpp/LeanCondensedMatter/issues/421) replaced competing finite weighted Gibbs functionals with `DensityOperator.expectation` as the physical normalized expectation. Finite traces, diagonal sums, and occupation-basis weights remain useful calculation or proof representations, isolated behind bridges; they are not alternative state models. It also extracted the minimal expectation/KMS first-pair contract from the concrete finite Gibbs proof. The generic pairing induction has no configuration type or `Fintype` assumption, allowing future implementations to state their own summability and domain obligations.
