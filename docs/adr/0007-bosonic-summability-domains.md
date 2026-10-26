---
status: accepted
---

# Make bosonic thermal summability a domain condition

A nonempty finite bosonic mode set still has infinitely many occupation configurations because each mode admits arbitrary natural-number occupation. Therefore finite-mode bosonic thermal theory uses an explicit summability domain rather than the finite-configuration trace argument available to finite-mode fermions.

`grandCanonicalGibbsDomain ε β μ` specializes `Common.summableDiagonalTraceDomain` to the shifted free-heat operator, while `Common.summableDiagonalTraceRatioLinear` supplies the state-independent partial linear trace ratio. The concrete bosonic membership equivalence and finite-sum adapter transport
explicit summability witnesses to that common linear map. The total trace-ratio
expression `grandCanonicalGibbsExpectation ε β μ` has physical expectation semantics only when its numerator is
summable and its partition series is nonzero. For free thermal field lists, the ordered-product
summability theorem establishes this domain condition for every finite product; the Common pairing
recursion therefore consumes the trace-ratio expression directly, without a second totalization.

Algebraic thermal statements retain explicit membership proofs independently of the completed-space realization. Linear closure does not imply closure under operator products or integrals. Those operations, and any later boundedness or trace-class interpretation, need separate analytic justification.

Finite-mode polynomial occupation majorants own weighted-monomial summability. Quadratic and total-particle-number bounds specialize them; ordered-product summability supplies shifted-power majorants. Exact particle-number sums remain separate where KMS arguments need the value.

`Bosonic.Algebra.LadderTraceCyclicity` owns occupation reindexing without Gibbs or KMS hypotheses; `Thermal.BlochDeDominicis.FreeKMSRotation` adds the thermal factors. Occupation inequalities stay in `Bosonic.Algebra.Occupation`; quartic pointwise bounds stay in `Perturbation.QuarticVertexBound`. `QuarticGibbsSummable` obtains domain membership from the ordered-product theorem. These finite-mode estimates do not establish an infinite-mode extension.

Evidence: [summability domain and expectation](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ConvergenceAwareGibbs.lean), [occupation algebra](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/Occupation.lean), [quartic coefficient bound](../../LeanCondensedMatter/SecondQuantization/Bosonic/Perturbation/QuarticVertexBound.lean), [quartic Gibbs adapter](../../LeanCondensedMatter/SecondQuantization/Bosonic/Perturbation/QuarticGibbsSummable.lean), and [bosonic thermal boundary](../roadmaps/thermal-expectation-architecture.md).

The [quadratic and total-number bounds](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/QuadraticParticleNumberWeightSummable.lean) share the polynomial majorants; [exact particle-number sums](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ParticleNumberWeightSummable.lean) and [KMS rotation](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BlochDeDominicis/FreeKMSRotation.lean) retain their separate roles.
