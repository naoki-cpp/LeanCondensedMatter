---
name: refactor-lean-proofs
description: Behavior-preserving refactor pass over this project's Lean files — find duplicated proof idioms, extract them as named lemmas, verify, and open a PR. Use when the user asks to refactor, clean up, or dedupe Lean code. Read the canonical workflow in `.agents/skills/refactor-lean-proofs/SKILL.md`.
---

# Shared Lean refactor pass

The canonical skill is repository-local and shared with Claude:

`.agents/skills/refactor-lean-proofs/SKILL.md`

Read and apply that file in full. Do not duplicate or reinterpret its workflow. In particular, present candidates and wait for approval before editing, and merge only when the user explicitly says to.
