---
status: accepted
---

# Use Lean and Mathlib as the mathematical foundation

The project formalizes condensed-matter results in Lean 4 and uses Mathlib as its only direct external Lean library. Reuse Mathlib structures and bundled maps where they express the intended mathematics, and keep the Lean toolchain and dependency revision pinned.

This makes general algebra and analysis available through one shared vocabulary instead of maintaining a parallel mathematical foundation. The cost is that library upgrades and changes to canonical upstream APIs require deliberate migration; a locally shorter bespoke construction does not by itself justify a competing public API.

Physical assumptions remain explicit in definitions or hypotheses, with provenance recorded where a modeling choice enters. Kernel checking establishes the stated mathematical implication; it does not establish that its physical hypotheses describe a particular experiment.

Evidence: [dependency configuration](../../lakefile.toml), [pinned dependencies](../../lake-manifest.json), [toolchain](../../lean-toolchain), and [conventions](../../notes/conventions.md).

## Historical evidence

[Issue #885](https://github.com/naoki-cpp/LeanCondensedMatter/issues/885) standardized public nonzero-position hypotheses to `j ≠ 0`, matching Mathlib's finite-deletion APIs. Align the authoritative interface with the library's predicate orientation instead of accumulating `Ne.symm` adapters at call sites or retaining a compatibility wrapper for the old orientation.

[Issue #882](https://github.com/naoki-cpp/LeanCondensedMatter/issues/882) removed the `FinCast` shim after its only theorem became a direct use of `Fin.castOrderIso`'s `StrictMono` property. Do not keep a project module or forwarding import solely to re-export a library fact; import the modules that own the APIs actually used.

[Issue #880](https://github.com/naoki-cpp/LeanCondensedMatter/issues/880) applied this rule to deletion reindexing in finite sums: use Mathlib's `finSuccAboveEquiv 0` instead of a private equivalence, adding only the predicate-orientation transport required by the existing statement. The public sum-decomposition theorem remains the semantic boundary while its proof plumbing follows the canonical library API.

[Issue #874](https://github.com/naoki-cpp/LeanCondensedMatter/issues/874) removed local induction for `List.Perm` invariance of a commutative list sum and reused Mathlib's big-operator lemmas. Preserve the public semantic length theorem while deleting private arithmetic scaffolding made redundant by the library.

[Issue #857](https://github.com/naoki-cpp/LeanCondensedMatter/issues/857) uses inherited `Fintype` instances for literal subtypes of finite types instead of rebuilding them through projection injectivity. Reuse the strongest canonical instance without adding unrelated decidability requirements.

[Issue #856](https://github.com/naoki-cpp/LeanCondensedMatter/issues/856) uses Mathlib's set/image equivalences for finite image subtypes instead of rebuilding an `Equiv` from manual injectivity and surjectivity proofs. Let canonical equivalence constructors carry the image membership invariant directly.

[Issue #852](https://github.com/naoki-cpp/LeanCondensedMatter/issues/852) applies the pinned-library rule to algorithms and proof plumbing: use Mathlib sorting, list-sum, finite-equivalence, and subtype-instance machinery where it already captures the mathematics. Keep project-local code for genuine domain content, not a second implementation of a general collection algorithm.

[Issue #823](https://github.com/naoki-cpp/LeanCondensedMatter/issues/823) used Mathlib's complement and image/subtype equivalences to express family-slot head/tail decomposition. Bundle the mathematical bijection directly instead of rebuilding membership, injectivity, and surjectivity case analyses around raw functions.

[Issue #821](https://github.com/naoki-cpp/LeanCondensedMatter/issues/821) combines two forms of proof reuse: expose only the general recurrence needed by low-order logarithm corollaries, and consume Mathlib's pinned empty-partition uniqueness/simp API instead of reconstructing it locally. Specializations should call an established general theorem; upstream facts should not be shadowed by project-local copies.

[Issue #820](https://github.com/naoki-cpp/LeanCondensedMatter/issues/820) broadens the upstream-reuse rule from definitions to proof structure: prefer canonical Mathlib equivalences, partition constructors, and integration results over hand-built bijection or finite-index plumbing. When a stronger general theorem exists, derive specializations from it rather than maintaining parallel inductions. Simplicity and the pinned APIs remain the constraint; avoid duplicate project abstractions.

[Issue #316](https://github.com/naoki-cpp/LeanCondensedMatter/issues/316) showed the project formal logarithm was definitionally identical to Mathlib's `PowerSeries.logOf`. The chosen boundary was one authoritative upstream definition, with only genuinely reusable partition-series normalization remaining project-owned. This avoids maintaining compatibility aliases after callers can migrate.

[Issue #315](https://github.com/naoki-cpp/LeanCondensedMatter/issues/315) required a Mathlib/API preflight before building analytic Dyson theory. It found the project formal-log wrapper definitionally identical to `PowerSeries.logOf`, and verified that finite-dimensional operator promotion, integration, exponentials, analytic power series, and ODE uniqueness already existed upstream. The decision was to remove duplicate constructions and validate the integral bridge, not to build an independent analysis stack. The survey is pinned to the revision examined there and should be revisited after dependency upgrades.

[Issue #257](https://github.com/naoki-cpp/LeanCondensedMatter/issues/257) gives a concrete reason to prefer an upstream equivalence even in a private helper: a locally defined sigma/product distribution duplicated `Equiv.sigmaProdDistrib` with reversed orientation. Its proposed replacement used `.symm` and the narrow required import while preserving consumer behavior. The enduring rule is to compose or reverse an existing bundled equivalence before adding another project-owned representation of the same map.

[PR #5](https://github.com/naoki-cpp/LeanCondensedMatter/pull/5) records an explicit Mathlib/PhysLean comparison for the moment–cumulant and Wick program. Mathlib supplied finite partitions and incidence algebras, so the project added the missing adapters. PhysLean's surveyed Wick construction addressed the zero-temperature case rather than the thermal-average target, and the project chose not to add that dependency. This is the recorded assessment at that point, not a claim about the present scope of another library.
