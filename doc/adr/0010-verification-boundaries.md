---
status: accepted
---

# Use Lean for semantic guarantees and source audits for architecture

Express mathematical identities and durable semantic guarantees in Lean definitions, types, and theorems. Use source architecture checks for module topology and explicit source contracts; use compiled environment audits as focused local tools for investigating elaborated API boundaries.

Declarative graphs encode allowed dependency direction, while source contracts separately encode required files or direct imports. Neither should become a catalogue of deleted paths or incidental proof syntax. The distinction permits proof refactoring while preserving the current architectural constraints.

CI combines selected source checks with Lean builds, linting, duplicate-declaration checks, and an independent `sorryAx` audit. More declaration-specific compiled architecture investigations remain local rather than becoming permanent regression checks. Source parsing cannot establish Lean semantics, and successful elaboration alone is not a substitute for rejecting proof placeholders.

Evidence: [audit responsibilities](../../scripts/architecture/README.md), [source audit entry point](../../scripts/check_architecture.py), [CI workflow](../../.github/workflows/lean_action_ci.yml), and [placeholder audit](../../scripts/CheckNoSorry.lean).
