# LeanCondensedMatter

> **IMPORTANT: The AI must not modify this file (PROJECT.md) autonomously without an explicit instruction from the user.**
> If a change seems necessary, propose it and obtain the user's approval before editing.
>
> This is the shared instruction file for all AI harnesses. `AGENTS.md` (Codex) and `CLAUDE.md` (Claude Code) both just point here — edit this file, not those.

## Purpose

Formalize results in condensed matter physics as machine-checked theorems in Lean 4, building on Mathlib where possible. The project keeps mathematical statements, physical assumptions, and their provenance clearly separated and documented.

## Document tree

```
PROJECT.md                 — this index: purpose, tree, writing rules (keep slim)
AGENTS.md / CLAUDE.md       — thin pointers to this file, for harness discovery
notes/
  roadmap.md               — formalization targets status table (index)
  roadmaps/
    quantum-theory-foundations.md — Track A detail
    combinatorics.md               — Track B detail
    operator-algebra.md            — Track C detail
    linked-cluster-theorem.md      — Combined target detail
  completed.md              — targets that have reached `proved`
  conventions.md           — Lean/Mathlib style and project conventions
  model-and-assumptions.md — physical models, assumptions, and how they map to formal definitions
  caveats.md               — known pitfalls and things to watch out for
  references.md            — annotated reference list
```

Details belong in `notes/`; do not add content sections to this file.

## Writing rules — notes (`notes/*.md`)

- **Every claim needs a source.** When stating a physical or mathematical claim, value, mechanism, or formula, cite its provenance (reference, equation number, Mathlib declaration name). Do not write claims you cannot source.
- **Separate the source's claims from your own inference.** Distinguish what a reference states from your interpretation or extrapolation; mark inference explicitly (e.g. "(inferred)"). Do not add words absent from the original when summarizing, and do not present open questions as settled.
- **When unsure, verify before writing.** Do not assert from memory; check the original source or the Lean code itself first.

## Writing rules — Lean code

- **Correctness is the kernel's job, not prose's.** Do not pad code with citation text to justify something the type checker already guarantees; sourcing is only needed where a definition encodes a physical assumption or choice that isn't forced by the math (see below).
- **Cite physical assumptions where they enter, not everywhere.** When a `def`/`structure`/hypothesis embeds a physical modeling choice (not a pure math fact), a short docstring/comment citing the source is warranted. Routine lemmas need no citation.
- **Formal vs. informal.** A statement is only "proved" when it compiles with no `sorry`; otherwise record it as a target or conjecture in `notes/roadmap.md`, not as a claim in prose.
- **Names and structures track the physics dictionary.** Keep `def`/`theorem` names aligned with the physical notions they formalize, per the physics-to-Lean dictionary in `notes/model-and-assumptions.md`; update that dictionary when a new correspondence is introduced.

## Commit conventions

- Commits follow Conventional Commits, in English. See `notes/conventions.md` for format and type/scope guidance.
