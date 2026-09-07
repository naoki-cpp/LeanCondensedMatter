---
name: refactor-lean-proofs
description: Behavior-preserving refactor pass over this project's Lean code — find duplicated proof idioms, hidden common structure, misplaced facts, and non-canonical APIs; extract or move them, verify, and open a PR. Use when the user asks to refactor, clean up, dedupe, or audit Lean code.
---

# Refactor Lean proofs

A behavior-preserving cleanup pass. Preserve the mathematics and physical meaning; improve where proofs, declarations, and responsibilities live and how shared structure is exposed.

## What to look for

Scan the target source scope, excluding generated and build artifacts, for these patterns in priority order:

1. **Duplicated proof blocks** — the same sequence of tactics or terms appearing in two or more declarations. Extract a named lemma at the most upstream layer that can state it, and make all occurrences delegate to it.
2. **Repeated inline idioms** — a nontrivial expression such as an instance derivation, cast bridge, or elementary fact repeated at several use sites. Extract a small named lemma next to its semantic subject.
3. **Misplaced general facts** — a declaration stated in a downstream or specific layer that is really about an upstream general structure. Move it to the earliest layer that owns its meaning; retain a downstream name only when compatibility is explicitly required.
4. **Parallel coordinate or case APIs** — declarations whose names, statements, or proofs differ only by an output coordinate, direction, branch, or finite index. Prefer one indexed or structured canonical declaration and specialize only at consumers. Typical smells are coordinate-paired theorems, coordinate-specific convergence theorems, and repeated selector wrappers. Before generalizing, verify that the candidates are actually projections of one object rather than independent invariants or coefficients.
5. **Split-then-reassemble APIs** — a richer mathematical object is decomposed into components and later reconstructed manually. Prefer propagating the whole object through the reusable layer: for example, a complex value instead of separate real and imaginary limits, a vector instead of separate coordinates, or a matrix or map instead of entrywise wrappers. Keep projections public only where the projection itself is an observable or independently useful statement.
6. **Hidden reusable mathematics inside domain-specific code** — calculus, algebra, continuity, integral, limit, or non-vanishing arguments that do not depend on the physical model. Extract them to the earliest mathematical owner and let model-specific code instantiate them. Repeated model-independent calculations are a strong signal that the common theorem belongs upstream.
7. **Semantic ownership or import inversions** — a foundational or model layer depends on a downstream response or observable layer merely to reuse a fact whose meaning is more general. Move the fact to the layer that owns its referent, then let downstream consumers depend on that owner. Treat import direction as evidence of misplaced responsibility, not merely as packaging.
8. **Mixed or artificial module boundaries** — split modules that combine distinct mathematical, model, response, or observable responsibilities. Conversely, collapse strict one-consumer chains whose intermediate modules only route proof stages and have no independent semantic API. Boundaries should follow semantic responsibility, not the historical order in which a proof was developed.
9. **Public proof plumbing** — public lemmas, exact-form intermediates, bridge theorems, or helper definitions with no external in-repository callers and no independent mathematical or physical meaning. Make them private or local, or inline them, so the public API exposes reusable concepts and physical endpoints rather than proof routing.
10. **Specialization and compatibility wrappers** — domain-specific declarations that merely instantiate a general theorem, forwarding aliases or imports, duplicate re-exports, or obsolete names kept only for historical packaging. Prefer using the canonical general declaration directly and migrate in-repository callers in the same refactor unless compatibility was explicitly requested.
11. **Coordinate formulas hiding invariant structure** — repeated low-level expressions may be components of a standard object. When antisymmetric combinations, determinant-like terms, dot-product expansions, matrix-entry formulas, or norm expansions recur, ask whether they should be stated once via the corresponding invariant structure and projected only where coordinates are required. Do not abstract from syntax alone: confirm that the variables really are coordinates of the same geometric or algebraic object.
12. **Duplicated limit or continuity transport** — several model-level convergence theorems repeat the same rational, coordinate, projection, or continuity argument after a shared input limit is known. Move the generic transport theorem to the algebraic owner and have the physical layer supply only the model-specific convergence hypotheses.

## Audit passes

Do not rely only on visually identical proof text. Run these conceptual passes over the target scope:

- **Name-family pass:** look for declaration families differing mainly by coordinate, real or imaginary part, longitudinal or transverse role, branch, or a small finite index. Compare signatures and callers to decide whether an index or structure is canonical.
- **Reconstruction pass:** search for consumers that combine separately proved components back into one richer object. If reconstruction is routine, the richer object probably belongs upstream.
- **Mathematics-owner pass:** inspect repeated derivative, integral, continuity, denominator, nonzero, and limit arguments. Strip away model parameters mentally and ask whether the remaining theorem is model-independent.
- **Dependency-direction pass:** inspect dependencies around suspicious facts. If a foundational layer reaches into a response or observable layer for a reusable fact, identify the lowest semantic owner that both sides can depend on.
- **Module-boundary pass:** summarize each module in one phrase. A module needing two unrelated phrases is a split candidate; a module whose phrase is only “forwards one proof stage to another” is a collapse candidate.
- **Public-surface pass:** for each exposed helper in the refactor target, check external in-repository callers. No callers plus no independent semantic content is evidence for making it private, not for preserving it as API.
- **Negative-control pass:** explicitly record why near-duplicates that remain separate are genuinely distinct. Independent scalar invariants, physically different observables, different hypotheses, or different asymptotic orders should not be forced into an index merely because their proofs look alike.

For every proposed candidate, record: the smell, concrete declarations or modules, the common mathematical or physical object, the proposed canonical owner or API, why the abstraction is reusable, and what should remain specialized. Prefer candidates that reduce competing APIs or reverse dependencies, not merely line count.

Do **not**:

- Merge proofs that merely look similar but differ in the quantities involved, independent invariants, or genuinely different hypotheses. Forced unification risks both semantic confusion and kernel timeouts.
- Introduce an indexed abstraction whose only purpose is to hide unrelated formulas behind a selector. The index should name a real mathematical family or structured object.
- Change the mathematical or physical meaning of a public declaration during a refactor. A public API rename, move, or generalization is allowed only when it preserves meaning and the user has approved that candidate; migrate in-repository callers completely.
- Modify permanent documentation unless the current architecture or documented API actually changes. Permanent documentation should describe the resulting repository, not refactor history.

## Workflow

Follow the project's standard cycle for every unit of work:

1. Make the edits.
2. Build the touched targets and iterate until zero errors.
3. Confirm no placeholders remain in touched source.
4. Run broader verification when required by the current project conventions.
5. Create a dedicated branch and pull request following the project commit conventions.
6. Merge only when the user explicitly says to and required checks pass, then synchronize the default branch.

For documentation-only changes, follow the project conventions and skip source builds when they are not required.

## Reporting

Before editing a refactor target, present the found candidates to the user with source locations, the proposed canonical owner or API, and the negative-control check, then wait for approval. After the PR is open, summarize what moved where and which competing APIs or dependency inversions were removed in one short list.
