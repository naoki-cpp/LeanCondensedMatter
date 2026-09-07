# LeanCondensedMatter

> **IMPORTANT: The AI must not modify this file (PROJECT.md) autonomously without an explicit instruction from the user.**
> If a change seems necessary, propose it and obtain the user's approval before editing.
>
> This is the shared instruction entry point for all AI harnesses. `AGENTS.md` (Codex) and `CLAUDE.md` (Claude Code) both just point here — edit this file, not those.

## Purpose

Formalize results in condensed matter physics as machine-checked theorems in Lean 4, building on Mathlib where possible. The project keeps mathematical statements, physical assumptions, and their provenance clearly separated and documented.

## Document tree

```text
PROJECT.md                  — this index: purpose, tree, and pointers (keep slim)
AGENTS.md / CLAUDE.md       — thin pointers to this file, for harness discovery
README.md                   — public repository entry point
notes/
  roadmap.md                — repository-wide target/status index
  completed.md              — major targets that have reached `proved`
  conventions.md            — project-wide coding, refactoring, proof, workflow, and commit rules
  model-and-assumptions.md  — physical models and physics-to-Lean dictionary
  caveats.md                — known pitfalls and boundaries
  references.md             — annotated external references
  architecture/             — stable subsystem boundaries and ownership rules
    second-quantization.md
    fermionic-field-operators.md
    quantum-density-theory.md
    physical-real-scalar-boundary.md
  examples/                 — worked examples tied to proved APIs
  glossary/                 — domain terminology and notation
  migrations/               — API migration notes when public interfaces change
  roadmaps/                 — detailed research/status documents by topic
    quantum-theory-foundations.md
    combinatorics.md
    operator-algebra.md
    fredholm-determinant.md
    second-quantization.md
    second-quantization-status.md
    thermal-expectation-architecture.md
    linked-cluster-theorem.md
    completed-space-and-infinite-mode.md
    transport.md
    impurity-vertex-correction.md
```

Project-wide implementation, documentation, refactoring, proof, dependency, workflow, and commit rules live in [`notes/conventions.md`](notes/conventions.md). Topic-specific details belong in `notes/`; do not add long content sections to this file.
