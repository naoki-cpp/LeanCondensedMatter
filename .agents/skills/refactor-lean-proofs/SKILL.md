---
name: refactor-lean-proofs
description: Behavior-preserving refactor pass over this project's Lean files — find duplicated proof idioms, hidden common structure, misplaced facts, and non-canonical APIs; extract or move them, verify, and open a PR. Use when the user asks to refactor, clean up, dedupe, or audit Lean code.
---

# Refactor Lean proofs

A behavior-preserving cleanup pass. Preserve the mathematics and physical meaning; improve where proofs, declarations, and responsibilities live and how shared structure is exposed.

## What to look for

Scan the project's `.lean` files (not `.lake/`) for, in priority order:

1. **Duplicated proof blocks** — the same sequence of tactics/terms appearing in two or more declarations, possibly across files. Extract as a named lemma in the most upstream file that can state it, and make all occurrences delegate to it.
2. **Repeated inline idioms** — a multi-token expression (instance derivation, cast bridge, norm fact) repeated at several use sites within a file. Extract as a small named lemma next to its subject.
3. **Misplaced general facts** — a lemma stated in a downstream/specific file that is really about an upstream general structure. Move it upstream; keep the downstream name only if other files already use it and compatibility is explicitly required for the task.
4. **Parallel coordinate or case APIs** — declarations whose names, statements, or proofs differ only by an output coordinate, direction, branch, or finite index. Prefer one indexed or structured canonical declaration and specialize only at consumers. Typical smells are X/Y theorem pairs, coordinate-specific convergence theorems, and repeated selector wrappers. Before generalizing, verify that the candidates are actually projections of one object rather than independent invariants or coefficients.
5. **Split-then-reassemble APIs** — a richer mathematical object is decomposed into coordinates and later reconstructed manually. Prefer propagating the whole object through the reusable layer: e.g. a complex value instead of separate real/imaginary limits, a vector instead of separate coordinate values, or a matrix/map instead of entrywise wrappers. Keep projections public only where the projection itself is the observable or independently useful statement.
6. **Hidden reusable mathematics inside physics modules** — calculus, algebra, continuity, integral, limit, or non-vanishing arguments that do not depend on the physical model. Extract them to `Analysis/` or the earliest mathematical owner and let model-specific code instantiate them. A repeated radial integral or antiderivative proof is a strong signal that the common theorem belongs upstream.
7. **Semantic ownership or import inversions** — an upstream/model/analysis module imports a downstream response or observable layer merely to reuse a fact whose meaning is more general. Move the fact to the layer that owns its referent, then let both downstream consumers depend on that owner. Inspect import direction as evidence of misplaced responsibility, not just file names.
8. **Mixed or artificial module boundaries** — split files that combine distinct mathematical, model, response, and observable responsibilities. Conversely, collapse strict one-consumer chains whose intermediate modules only route proof stages and have no independent semantic API. File boundaries should follow semantic responsibility, not the historical order in which a proof was developed.
9. **Public proof plumbing** — public lemmas, exact-form intermediates, bridge theorems, or helper definitions with no external in-repository callers and no independent mathematical or physical meaning. Make them `private`/local or inline them so the public API exposes reusable concepts and physical endpoints rather than proof routing.
10. **Specialization and compatibility wrappers** — domain-specific declarations that merely instantiate a general theorem, forwarding aliases/imports, duplicate re-exports, or obsolete names kept only for historical packaging. Prefer using the canonical general declaration directly and migrate in-repository callers in the same refactor unless compatibility was explicitly requested.
11. **Coordinate formulas hiding invariant structure** — repeated low-level expressions may be components of a standard object. When expressions such as antisymmetric combinations (`x₁*y₂ - x₂*y₁`), determinant-like terms, dot-product expansions, matrix-entry formulas, or norm expansions recur, ask whether they should be stated once via the corresponding invariant structure (e.g. exterior/cross-product component, determinant, inner product, linear map) and projected only where coordinates are required. Do not abstract from syntax alone: confirm the variables really are coordinates of the same geometric/algebraic object.
12. **Duplicated limit/continuity transport** — several model-level convergence theorems repeat the same rational, coordinate, projection, or continuity argument after a shared input limit is known. Move the generic continuity/limit transport theorem to the algebraic owner and have the physical layer supply only the model-specific convergence hypotheses.

## Audit passes

Do not rely only on visually identical proof text. Run these conceptual passes over the target scope:

- **Name-family pass:** look for declaration families differing mainly by `X`/`Y`, `Re`/`Im`, `Longitudinal`/`Transverse`, coordinate names, branch names, or a small finite index. Compare signatures and callers to decide whether an index/structure is canonical.
- **Reconstruction pass:** search for consumers that combine separately proved components back into one complex/vector/matrix expression. If reconstruction is routine, the richer object probably belongs upstream.
- **Mathematics-owner pass:** inspect repeated derivative, integral, continuity, algebraic denominator, nonzero, and limit arguments. Strip away model parameters mentally and ask whether the remaining theorem is model-independent.
- **Dependency-direction pass:** inspect imports around suspicious facts. If a foundational layer reaches into a response/observable layer for a reusable fact, identify the lowest semantic owner that both sides can import.
- **Module-boundary pass:** summarize each file in one phrase. A file needing two unrelated phrases is a split candidate; a file whose phrase is only “forwards stage A to stage B” is a collapse candidate.
- **Public-surface pass:** for each helper exposed by a refactor target, check external in-repository callers. No callers plus no independent semantic content is evidence for making it private, not for preserving it as API.
- **Negative-control pass:** explicitly record why near-duplicates that remain separate are genuinely distinct. Independent scalar invariants, physically different observables, different hypotheses, or different asymptotic orders should not be forced into an index merely because their proofs look alike.

For every proposed candidate, record: the smell, concrete declarations/files, the common mathematical or physical object, the proposed canonical owner/API, why the abstraction is reusable, and what should remain specialized. Prefer candidates that reduce competing APIs or reverse dependencies, not merely line count.

Do **not**:

- Merge proofs that merely *look* similar but differ in the quantities involved (signs, norms vs. inner products, independent invariants, or genuinely different hypotheses) — forced unification risks both semantic confusion and kernel timeouts; see `notes/caveats.md` and the cautions in `notes/conventions.md` (Proof style).
- Introduce an indexed abstraction whose only purpose is to hide two unrelated formulas behind a selector. The index should name a real mathematical family or structured object.
- Change the mathematical or physical meaning of a public declaration during a refactor. A public API rename/move/generalization is allowed only when it preserves meaning and the user has approved that candidate; migrate in-repository callers completely.
- Touch `notes/` content except where the current architecture or documented API actually changes; permanent notes describe the resulting repository, not refactor history.

## Workflow

Follow the project's standard cycle for every unit of work:

1. Make the edits.
2. `lake build <touched targets>` as a background task; iterate until zero errors. Expect Lean builds to take minutes — schedule wakeups rather than polling.
3. Confirm no `sorry` in touched files.
4. Full `lake build` when required by the current project conventions.
5. Branch off `main` (`refactor/<slug>`), commit (Conventional Commits, English, type `refactor`), push, `gh pr create`.
6. **Merge only when the user explicitly says to**, and only after `gh pr checks` passes; use `gh pr merge --squash --delete-branch`, then sync local `main`.

For documentation-only changes, follow `notes/conventions.md`: do not run a Lean build when only comments/Markdown/skill documentation changed.

## Reporting

Before editing a refactor target, present the found candidates to the user with file/line references, the proposed canonical owner/API, and the negative-control check, then wait for approval. After the PR is open, summarize what moved where and which competing APIs or dependency inversions were removed in one short list.
