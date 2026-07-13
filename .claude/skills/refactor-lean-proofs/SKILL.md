---
name: refactor-lean-proofs
description: Behavior-preserving refactor pass over this project's Lean files — find duplicated proof idioms, extract them as named lemmas, verify, and open a PR. Use when the user asks to refactor, clean up, or dedupe Lean code (「リファクタ」).
---

# Refactor Lean proofs

A behavior-preserving cleanup pass. No statement may change meaning; only where a proof lives and how it is shared.

## What to look for

Scan the project's `.lean` files (not `.lake/`) for, in priority order:

1. **Duplicated proof blocks** — the same sequence of tactics/terms appearing in two or more declarations, possibly across files. Extract as a named lemma in the most upstream file that can state it, and make all occurrences delegate to it.
2. **Repeated inline idioms** — a multi-token expression (instance derivation, cast bridge, norm fact) repeated at several use sites within a file. Extract as a small named lemma next to its subject.
3. **Misplaced general facts** — a lemma stated in a downstream/specific file that is really about an upstream general structure. Move it upstream; keep the downstream name only if other files already use it.

Do **not**:

- Merge proofs that merely *look* similar but differ in the quantities involved (signs, norms vs. inner products) — forced unification risks kernel timeouts; see `notes/caveats.md` and the cautions in `notes/conventions.md` (Proof style).
- Change any statement, hypothesis set, or namespace of an existing public declaration without flagging it to the user first.
- Touch `notes/` content except to record what moved.

## Workflow

Follow the project's standard cycle for every unit of work:

1. Make the edits.
2. `lake build <touched targets>` as a background task; iterate until zero errors. Expect Lean builds to take minutes — schedule wakeups rather than polling.
3. Confirm no `sorry` in touched files.
4. Full `lake build`.
5. Branch off `main` (`refactor/<slug>`), commit (Conventional Commits, English, type `refactor`), push, `gh pr create`.
6. **Merge only when the user explicitly says to**, and only after `gh pr checks` passes; use `gh pr merge --squash --delete-branch`, then sync local `main`.

## Reporting

Before editing, present the found candidates to the user with file/line references and wait for approval. After the PR is open, summarize what moved where in one short list.
