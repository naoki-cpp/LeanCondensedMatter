---
status: accepted
---

# Make bosonic thermal summability a domain condition

A nonempty finite bosonic mode set still has infinitely many occupation configurations because each mode admits arbitrary natural-number occupation. Therefore finite-mode bosonic thermal theory uses an explicit summability domain rather than the finite-configuration trace argument available to finite-mode fermions.

`ConvergenceAwareGibbsFunctional` stores a submodule of admissible observables and a normalized linear expectation on that submodule. Its totalized value is an adapter for total-function interfaces; the assigned value outside the domain is not a physical expectation.

This lets algebraic thermal results proceed before a completed bosonic operator theory is available, at the cost of explicit membership proofs. Linear closure does not imply closure under operator products or integrals. Those operations, and any later boundedness or trace-class interpretation, need separate analytic justification.

Evidence: [domain and totalization](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ConvergenceAwareGibbs.lean) and [bosonic thermal boundary](../../notes/roadmaps/thermal-expectation-architecture.md).
