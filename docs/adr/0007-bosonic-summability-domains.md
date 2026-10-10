---
status: accepted
---

# Make bosonic thermal summability a domain condition

A nonempty finite bosonic mode set still has infinitely many occupation configurations because each mode admits arbitrary natural-number occupation. Therefore finite-mode bosonic thermal theory uses an explicit summability domain rather than the finite-configuration trace argument available to finite-mode fermions.

`freeGibbsDomain` is the canonical submodule defined by `freeGibbsSummable`, and
`freeGibbsExpectationLinear` is the normalized expectation restricted to that submodule under
positive one-mode Boltzmann exponents. Its membership equivalence and finite-sum adapter convert
explicit summability witnesses into the subtype consumed by the linear map. The total trace-ratio
expression `freeGibbsExpectation` has physical expectation semantics only when its numerator is
summable and its partition series is nonzero. For free thermal field lists, the ordered-product
summability theorem establishes this domain condition for every finite product; the Common pairing
recursion therefore consumes the trace-ratio expression directly, without a second totalization.

This lets algebraic thermal results proceed before a completed bosonic operator theory is available, at the cost of explicit membership proofs. Linear closure does not imply closure under operator products or integrals. Those operations, and any later boundedness or trace-class interpretation, need separate analytic justification.

Finite-mode polynomial occupation majorants are owned by a general weighted-monomial summability layer; quadratic and total-particle-number bounds are specializations that consume it. Exact particle-number sum formulas remain separately available where KMS arguments need the value, rather than only convergence.

Evidence: [summability domain and expectation](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ConvergenceAwareGibbs.lean), [occupation algebra](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/Occupation.lean), [quartic coefficient bound](../../LeanCondensedMatter/SecondQuantization/Bosonic/Perturbation/QuarticVertexBound.lean), [quartic Gibbs adapter](../../LeanCondensedMatter/SecondQuantization/Bosonic/Perturbation/QuarticGibbsSummable.lean), and [bosonic thermal boundary](../roadmaps/thermal-expectation-architecture.md).

## Historical evidence

[Issue #2409](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2409) makes finite-mode polynomial occupation summability the upstream owner for Bosonic Gibbs majorants. The quadratic occupation-square theorem specializes the general monomial estimate, the total-particle-number square expands through those quadratic estimates, and ordered-product summability retains the shifted-power interface. Exact particle-number sums stay in their dedicated module for KMS consumers. This dependency order preserves finite-mode hypotheses and the genuinely infinite occupation space. Current sources: [polynomial owner](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/PolynomialOccupationWeightSummable.lean), [quadratic specialization](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/QuadraticParticleNumberWeightSummable.lean), [total-number specialization](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/TotalParticleNumberWeightSummable.lean), and [exact particle-number sum](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ParticleNumberWeightSummable.lean). The issue is closed.

[Issue #2408](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2408) separates bosonic occupation reindexing from the positive-energy Gibbs/KMS adapter. `Bosonic.Algebra.LadderTraceCyclicity` owns the two diagonal `tsumTrace` ladder-cyclicity results without Gibbs weights, energy, inverse temperature, or KMS factors; `FreeKMSRotation` combines those results with the imaginary-time shifts and retains the Bosonic thermal factors. This keeps coordinate transport below the analytic Gibbs layer and leaves infinite-sum assumptions explicit. Current source: [ladder trace cyclicity](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/LadderTraceCyclicity.lean) and [free Gibbs KMS rotation](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BlochDeDominicis/FreeKMSRotation.lean). The issue is closed.

[Issue #2407](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2407) makes the convergence-aware module the analytic adapter between a free-Gibbs summability proof, `freeGibbsDomain` membership, and normalized expectation evaluation. The canonical membership equivalence and finite-sum adapter remove repeated subtype/evaluation plumbing, while callers still supply each summability witness. Products and integrals do not gain domain closure without their own analytic proofs; the infinite occupation space is not replaced by a finite trace. Current source: [convergence-aware Gibbs domain and adapters](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ConvergenceAwareGibbs.lean), [peel consumer](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BlochDeDominicis/FreePeelIndexed.lean), and [interaction-picture consumer](../../LeanCondensedMatter/SecondQuantization/Bosonic/Perturbation/GibbsInteractionPicture.lean). The issue is closed.

[Issue #435](https://github.com/naoki-cpp/LeanCondensedMatter/issues/435) validates the boundary with a full finite-order bosonic perturbation slice: explicit admissible Gibbs observables and KMS hypotheses, polynomial-growth summability for quartic terms, recursive domain/product closure, and a separate expectation/integral interchange boundary. Common component combinatorics is reused, while the analytic convergence claims remain staged after the coefficientwise connected theorem; a completed Hilbert-Fock theory remains separate. The finite reachable-support construction is recorded in ADR 0005.

[Issue #345](https://github.com/naoki-cpp/LeanCondensedMatter/issues/345) explicitly kept `Bosonic.Perturbation` absent until a convergence-aware interface could justify it. A symmetric folder tree is not sufficient reason to expose an analytic API whose summability and domain requirements have not been proved. The directory layout follows semantic capability, not visual symmetry.

[Issue #318](https://github.com/naoki-cpp/LeanCondensedMatter/issues/318) explicitly kept the finite trace-series abstraction away from infinite bosonic occupations. Finite mode labels do not make the bosonic configuration type finite. The finite Common layer therefore remains parameterized by `[Fintype Config]`; a bosonic extension must provide infinite-sum and convergence hypotheses rather than erase that distinction.

[Issue #421](https://github.com/naoki-cpp/LeanCondensedMatter/issues/421) gives the corresponding reusable thermal boundary: expectation/KMS pairing induction is generic and has no finite configuration assumption, while a bosonic instance must supply its convergence-aware domain and closure proofs. Keeping the combinatorial recurrence independent of those analytic details allows a sound bosonic implementation without pretending its occupation sum is finite.

[Issue #2379](https://github.com/naoki-cpp/LeanCondensedMatter/issues/2379) reinforces the separation between pointwise occupation algebra and thermal convergence. The finite occupation inequalities and particle-number changes belong to `Bosonic.Algebra.Occupation`; the operator-specific quartic diagonal estimate retains the sharp `(N + 2)^2` growth in `Bosonic.Perturbation.QuarticVertexBound` without importing thermal summability. `QuarticGibbsSummable` obtains domain membership directly from the general finite ordered-product summability theorem; the sharp pointwise estimate remains a separate algebraic result. These perturbation results remain stated for finite mode types; this boundary does not establish an infinite-mode extension.
