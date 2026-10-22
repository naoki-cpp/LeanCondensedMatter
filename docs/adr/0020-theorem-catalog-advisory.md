---
status: accepted
---

# Keep theorem-catalog findings advisory

The Lean-generated theorem catalog is the full declaration inventory; related audits may flag declarations with no compiled proof reference, low consumer counts, candidate theorem substitutions, or candidate subproof ranges as review prompts, but these signals do not justify automatic API deletion or required pull-request gates because source-level use and semantic value need human review. Keep generated extension declarations in the full inventory but exclude them from unresolved queues; the retained-theorem registry is a reauditable exception list whose entries should be revisited when declarations or their consumers change.

Retained re-audit reports now distinguish persistent structural signals from evidence that changed since the last successfully published `graph-data` snapshot: theorem statement, module, compiled consumers, simp membership, wrapper target, terminal status, axiom provenance, and project/Mathlib theorem-replacement candidates. The comparison is a CI advisory summary and downloadable JSON; it is not proof of unused declarations, nor a record of the last human semantic review. Missing or invalid retained names remain compilation-catalog consistency errors. If the baseline snapshot is unavailable, report current structural queues without claiming a change history. Do not make these heuristics a required PR gate.

Evidence: [theorem catalog](../../scripts/TheoremCatalog.lean), [replacement audit](../../scripts/TheoremReplacementAudit.lean), [proof-region audit](../../scripts/ProofRegions.lean), [retained-theorem rationale](../theorem-catalog-retained.md), and [catalog workflows](../../scripts/architecture/README.md). The issue and PR rationale, including the open catalog-provenance work, is indexed in [history-review.md](history-review.md) (#2099, #2235, #2237, and #2767).
