---
status: accepted
---

# Make bosonic thermal summability a domain condition

A nonempty finite bosonic mode set still has infinitely many occupation configurations because each mode admits arbitrary natural-number occupation. Therefore finite-mode bosonic thermal theory uses an explicit summability domain rather than the finite-configuration trace argument available to finite-mode fermions.

`ConvergenceAwareGibbsFunctional` stores a submodule of admissible observables and a normalized linear expectation on that submodule. Its totalized value is an adapter for total-function interfaces; the assigned value outside the domain is not a physical expectation.

This lets algebraic thermal results proceed before a completed bosonic operator theory is available, at the cost of explicit membership proofs. Linear closure does not imply closure under operator products or integrals. Those operations, and any later boundedness or trace-class interpretation, need separate analytic justification.

Evidence: [domain and totalization](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ConvergenceAwareGibbs.lean) and [bosonic thermal boundary](../../notes/roadmaps/thermal-expectation-architecture.md).

## Historical evidence

[Issue #435](https://github.com/naoki-cpp/LeanCondensedMatter/issues/435) validates the boundary with a full finite-order bosonic perturbation slice: explicit admissible Gibbs observables and KMS hypotheses, polynomial-growth summability for quartic terms, recursive domain/product closure, and a separate expectation/integral interchange boundary. Common component combinatorics is reused, while the analytic convergence claims remain staged after the coefficientwise connected theorem; a completed Hilbert-Fock theory remains separate. The finite reachable-support construction is recorded in ADR 0005.

[Issue #345](https://github.com/naoki-cpp/LeanCondensedMatter/issues/345) explicitly kept `Bosonic.Perturbation` absent until a convergence-aware interface could justify it. A symmetric folder tree is not sufficient reason to expose an analytic API whose summability and domain requirements have not been proved. The directory layout follows semantic capability, not visual symmetry.

[Issue #318](https://github.com/naoki-cpp/LeanCondensedMatter/issues/318) explicitly kept the finite trace-series abstraction away from infinite bosonic occupations. Finite mode labels do not make the bosonic configuration type finite. The finite Common layer therefore remains parameterized by `[Fintype Config]`; a bosonic extension must provide infinite-sum and convergence hypotheses rather than erase that distinction.

[Issue #421](https://github.com/naoki-cpp/LeanCondensedMatter/issues/421) gives the corresponding reusable thermal boundary: expectation/KMS pairing induction is generic and has no finite configuration assumption, while a bosonic instance must supply its convergence-aware domain and closure proofs. Keeping the combinatorial recurrence independent of those analytic details allows a sound bosonic implementation without pretending its occupation sum is finite.
