---
status: accepted
---

# Use Lean and Mathlib as the mathematical foundation

The project formalizes condensed-matter results in Lean 4 and uses Mathlib as its only direct external Lean library. Reuse Mathlib structures and bundled maps where they express the intended mathematics, and keep the Lean toolchain and dependency revision pinned.

This makes general algebra and analysis available through one shared vocabulary instead of maintaining a parallel mathematical foundation. The cost is that library upgrades and changes to canonical upstream APIs require deliberate migration; a locally shorter bespoke construction does not by itself justify a competing public API.

Physical assumptions remain explicit in definitions or hypotheses, with provenance recorded where a modeling choice enters. Kernel checking establishes the stated mathematical implication; it does not establish that its physical hypotheses describe a particular experiment.

Evidence: [dependency configuration](../../lakefile.toml), [pinned dependencies](../../lake-manifest.json), [toolchain](../../lean-toolchain), and [conventions](../conventions.md).

## Scope of project-owned infrastructure

The project owns the fixed-scalar exchange bracket `[A,B]ζ = AB − ζ BA` in
[Analysis/ScalarExchange](../../LeanCondensedMatter/Analysis/ScalarExchange.lean).
Reuse this general algebraic interface across exchange-algebra consumers rather than copying
the bracket into each physical domain.

Consult the [pinned-Mathlib survey](../analysis-mathlib-audit.md) before extending analytical
infrastructure, and re-check its conclusions after dependency upgrades. The dependency choice
does not imply any claim about the present scope of other Lean libraries.
