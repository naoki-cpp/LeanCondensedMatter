---
status: accepted
---

# Keep theorem-catalog findings advisory

The Lean-generated theorem catalog is the full declaration inventory; related audits may flag declarations with no compiled proof reference, low consumer counts, candidate theorem substitutions, or candidate subproof ranges as review prompts, but these signals do not justify automatic API deletion or required pull-request gates because source-level use and semantic value need human review. Keep generated extension declarations in the full inventory but exclude them from unresolved queues; the retained-theorem registry is a reauditable exception list whose entries should be revisited when declarations or their consumers change.

Retained re-audit reports reuse the Lean catalog's `retainedNeedsReview` disposition as
the authoritative structural signal. They summarize declarations with no current signal,
zero compiled consumers, direct wrappers, and proof-guided replacement candidates. They
also compare review evidence (statements, owning modules, consumers, simp status, wrappers,
axiom provenance, and candidate replacements) against the previously published
`graph-data/theorems.json` snapshot. This is **not** a last-human-review baseline, nor
proof that a declaration is unused. Missing or invalid snapshots fall back to current
structural queues. All findings remain advisory, with no automatic deletion or new
heuristic required gate.

Evidence: [theorem catalog](../../scripts/TheoremCatalog.lean), [replacement audit](../../scripts/TheoremReplacementAudit.lean), [proof-region audit](../../scripts/ProofRegions.lean), [retained-theorem rationale](../theorem-catalog-retained.md), and [catalog workflows](../../scripts/architecture/README.md). The issue and PR rationale, including the open catalog-provenance work, is indexed in [history-review.md](history-review.md) (#2099, #2235, #2237, and #2767).
