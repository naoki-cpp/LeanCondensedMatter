# Conventions

Lean/Mathlib style and project-wide conventions.

## Naming

(To be filled)

## Project structure

(To be filled)

## Proof style

General cautions distilled from past sessions; detailed incident records live in `caveats.md`.

- **Abbreviations made with `have`/`haveI` are opaque.** They are not definitionally equal to the term they abbreviate. When a later step needs to unfold back to the original term, use `let`/`set`, or repeat the term at each use site.
- **Do not reindex a dependent `Sigma` index type through an `Equiv`.** Cast-based equivalences on dependent types risk genuine kernel timeouts even when they type-check. Reindex only the (non-dependent) base type, or split the sum into base and fiber parts instead.
- **Take analytic side conditions as explicit hypotheses.** When a definition needs compactness, summability, non-vanishing, or similar facts that do not follow from the ambient structure, accept them as arguments rather than deriving them — unless the derivation is itself a stated target.
- **Search Mathlib by compiling, not only by text.** When a lemma or instance is hard to locate by name, write a scratch file probing with `#check`/`#synth`/`exact?` and build it; delete the file afterwards.
- **Extend additively.** When generalizing an existing formalization (e.g. beyond a restrictive typeclass), add a parallel file/namespace; leave the original untouched.
- **Name recurring proof idioms.** When the same proof block appears in more than one declaration, extract it as a named lemma in the most upstream file that can state it.

## Dependencies

(To be filled)

## Commit conventions

- **Format:** [Conventional Commits](https://www.conventionalcommits.org/) — `type(scope): summary`, imperative mood, summary line kept short. Add a body when the "why" needs explanation.
- **Language:** English, regardless of the language used in chat/discussion.
- **Common types:** `feat` (new definition/theorem/proof), `fix` (correction to a definition or proof), `docs` (notes/ or root-level docs only), `refactor`, `chore` (tooling, deps, CI).
- **Scope:** name the affected area, e.g. `roadmap`, `conventions`, or a Lean module/namespace once source files exist.
