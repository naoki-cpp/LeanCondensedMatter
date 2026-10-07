---
status: accepted
---

# Treat global simp rules as canonical normal-form commitments

Lean's global simp set is the rewrite set applied implicitly by ordinary `simp`; register a theorem there only when its right-hand side is the stable, preferred normal form that downstream users should receive without choosing the rewrite explicitly. Keep substantive transformations, equally natural forms, and proof-local helpers available for explicit or local use, and use the [simp-boundary registry](../simp-boundaries.md) to record the current reviewed surface; compiled builds are needed to detect implicit simp dependencies when removing a rule.

Evidence: [project simplification conventions](../conventions.md), [reviewed simp-boundary registry](../simp-boundaries.md). The issue and PR progression from lint review through the repository-wide normal-form audit is indexed in [history-review.md](history-review.md) (#513, #525, #2678, #2696, #2750, and #2752).
