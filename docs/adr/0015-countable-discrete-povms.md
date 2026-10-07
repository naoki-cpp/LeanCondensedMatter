---
status: accepted
---

# Normalize countable discrete measurements pointwise

Represent a countable discrete POVM with one canonical `POVM` type: positive bounded effects indexed by `[Countable M]`, normalized by pointwise `HasSum` on every Hilbert-space vector. This strong operator normalization supports the Born-probability proof with the pinned Mathlib APIs; operator-norm summability is a stronger and unnecessary condition. Outcome countability does not imply finite Hilbert-space dimension.

Use the canonical density-operator expectation for each Born probability. Establish summability and total probability one through nonnegative series and the density spectral sum, then recover finite-outcome normalization as a specialization of the same API. Encode probabilities first as self-adjoint complex scalars and transport them losslessly to `ℝ`.

This slice covers discrete countable outcomes and bounded effects. General measurable-outcome POVMs, unbounded observables, and Naimark dilation require separate foundations.

Evidence: [POVM definition](../../LeanCondensedMatter/QuantumTheory/POVM/Basic.lean), [Born probabilities](../../LeanCondensedMatter/QuantumTheory/POVM/Born.lean), and [fiberwise infinite-sum lemmas](../../LeanCondensedMatter/Analysis/InfiniteSum/Fiberwise.lean).

## Historical evidence

[Issue #481](https://github.com/naoki-cpp/LeanCondensedMatter/issues/481) generalized the existing finite-outcome `POVM` itself to countable outcome types rather than introducing a parallel `CountablePOVM`. It selected strong pointwise normalization, proved the Born probabilities sum to one by exchanging nonnegative summable families, and retained finite outcomes as a specialization. This decision is independent of Hilbert-space dimension and does not imply a measurable-space or unbounded-observable theory.
