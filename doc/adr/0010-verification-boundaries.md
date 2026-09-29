---
status: accepted
---

# Use Lean for semantic guarantees and source audits for architecture

Express mathematical meaning in Lean definitions, types, and theorems; use source audits for files, imports, dependency direction, and explicit source contracts, and compiled-environment audits for declaration, namespace, and type-level contracts. Architecture CI protects current dependency direction and public-boundary imports, while selecting source-topology checks and Lean builds independently from changed files; compiled correctness and proof-placeholder checks remain explicit, and declaration-specific investigations stay local unless a stable invariant is deliberately selected for CI.

Evidence: [audit responsibilities](../../scripts/architecture/README.md), [source audit entry point](../../scripts/check_architecture.py), [source topology graphs](../../scripts/architecture/source_topology.json), [fixed source contracts](../../scripts/architecture/source_contracts.json), [compiled declaration audit](../../scripts/CheckArchitecture.lean), [CI workflow](../../.github/workflows/lean_action_ci.yml), and [placeholder audit](../../scripts/CheckNoSorry.lean). The issue/PR sequence for dependency ownership, audit boundaries, and CI routing is indexed in [history-review.md](history-review.md) (#2, #352, #1584, #1608, #2565, and #2567). The separate policy that keeps theorem-catalog signals outside required PR gates is recorded in [ADR 0020](0020-theorem-catalog-advisory.md).
