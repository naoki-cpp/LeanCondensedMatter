---
status: accepted
---

# Preserve reality and positivity at physical scalar boundaries

A physical quantity that is mathematically real should expose the proof of reality before being transported from complex scalars. Use the self-adjoint scalar equivalence for lossless conversion, stronger nonnegative types for probabilities, and extended nonnegative reals for entropy that may diverge.

Taking an arbitrary complex expression's real part would silently discard information and could hide a missing self-adjointness hypothesis. The stronger boundary costs additional proof work but lets downstream users rely on reality or positivity and recover the original complex value exactly. Real-part projection remains appropriate when the real component itself is the intended quantity.

The canonical APIs include real observable expectations, `probNNReal` and `bornPMF` for discrete measurements, and `vonNeumannEntropy : ENNReal`. Their codomains express different guarantees; finite entropy requires a separate finiteness result.

Evidence: [physical scalar policy](../../notes/architecture/physical-real-scalar-boundary.md), [observable definitions](../../LeanCondensedMatter/QuantumTheory/Postulates.lean), [entropy definition](../../LeanCondensedMatter/QuantumTheory/Entropy/Basic.lean), and [measurement architecture](../../notes/architecture/quantum-density-theory.md).

## Historical evidence

[Issue #553](https://github.com/naoki-cpp/LeanCondensedMatter/issues/553) preserves complex expectations for arbitrary bounded operators while exposing real-valued observable expectations only after a self-adjointness proof and lossless scalar transport. Born probabilities use `NNReal` and `PMF`; countable-basis diagonal formulas use explicit `tsum` summability, with finite-trace statements left as coordinate bridges. A repository audit rejects public physical definitions that discard information through `.re`; proof-local real extraction remains valid after an equality is established.

[Issue #432](https://github.com/naoki-cpp/LeanCondensedMatter/issues/432) records the Gibbs-equality work's need for exact equality cases, trace saturation, and full-support consequences. The implementation first made diagonal expectations and trace-series APIs losslessly real, then proved equality at each analytic step. Projecting through `.re` would discard the equality information these arguments need. The same issue coordinated finite LCT, purity, entropy, and Gibbs programs while keeping their roadmaps independent.

[PR #4](https://github.com/naoki-cpp/LeanCondensedMatter/pull/4) encountered the difference between a total mathematical function and its intended physical domain: `Real.log 0 = 0` made an unrestricted relative-entropy interpretation inappropriate, so its finite-dimensional inequality required strictly positive reference eigenvalues. That historical theorem is not the current entropy API, but the design constraint survives: totalized functions do not remove support, finiteness, or positivity obligations. In particular, converting extended entropy to a real value requires a finiteness justification.
