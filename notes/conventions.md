# Conventions

Lean/Mathlib style and project-wide conventions.

## Naming

- **Follow Mathlib's naming conventions.** `UpperCamelCase` for types, structures, and `Prop`-valued classes/predicates; `lowerCamelCase` for definitions; `snake_case` theorem names that describe the conclusion, with `_of_` introducing hypotheses.
- **Declarations live in the namespace of their subject.** General operator facts under the relevant Mathlib namespace (e.g. `ContinuousLinearMap`); physics-level content under `QuantumTheory` and its subnamespaces.
- **Parallel generalizations mirror the original's names.** An infinite-dimensional (or otherwise generalized) counterpart keeps the finite-dimensional declaration's name inside a distinguishing subnamespace, so the correspondence is visible from the name alone.
- **Physics names track the dictionary** in `model-and-assumptions.md` (see `PROJECT.md`).

## Project structure

- **One directory per track:** `Analysis/` for general mathematical infrastructure (Track C), `Combinatorics/` for Track B, `QuantumTheory/` for the physics postulates and what is built on them (Track A), `SecondQuantization/` for Track D (Fock space, creation/annihilation, CCR/CAR — kept separate from `QuantumTheory/` since second quantization is its own construction, not an extension of the axiomatic single-particle postulates). Physics files import analysis files, never the reverse.
- **Lemmas live as far upstream as they can be stated.** A fact about a general structure belongs in the infrastructure file, not in the physics file that first needed it.
- **Generalizations get a parallel file**, named after the original plus the enabling machinery, leaving the original file untouched.
- **Every unit of work updates its track's roadmap** (`notes/roadmaps/*.md`) in the same PR: what was proved, the route taken, and what remains.

## Proof style

General cautions distilled from past sessions; detailed incident records live in `caveats.md`.

- **Abbreviations made with `have`/`haveI` are opaque.** They are not definitionally equal to the term they abbreviate. When a later step needs to unfold back to the original term, use `let`/`set`, or repeat the term at each use site.
- **Do not reindex a dependent `Sigma` index type through an `Equiv`.** Cast-based equivalences on dependent types risk genuine kernel timeouts even when they type-check. Reindex only the (non-dependent) base type, or split the sum into base and fiber parts instead.
- **Take analytic side conditions as explicit hypotheses.** When a definition needs compactness, summability, non-vanishing, or similar facts that do not follow from the ambient structure, accept them as arguments rather than deriving them — unless the derivation is itself a stated target.
- **Search Mathlib by compiling, not only by text.** When a lemma or instance is hard to locate by name, write a scratch file probing with `#check`/`#synth`/`exact?` and build it; delete the file afterwards.
- **Extend additively.** When generalizing an existing formalization (e.g. beyond a restrictive typeclass), add a parallel file/namespace; leave the original untouched.
- **Name recurring proof idioms.** When the same proof block appears in more than one declaration, extract it as a named lemma in the most upstream file that can state it.

## Lean workflow

- Never run Lean against the entire project unless explicitly necessary.
- Compile only the currently edited file.
- Limit command output to the first relevant error.
- **Filter `lake build` output before reading it — do not rely on `tail` alone.** A single `trace:
  .> LEAN_PATH=...` line lists every dependency's absolute path and can dwarf the actual error in
  characters, even though it's one line; `tail -N` does not shrink it. Drop lines matching
  `^(trace:|Some required targets logged failures:|- LeanCondensedMatter\.|error: build failed$)`
  (e.g. `| grep -vE '...'` in bash, `Where-Object` in PowerShell) and keep: file:line:col, the
  failed tactic, the pattern it searched for, and the full goal/local context. Fix the first error
  before reading later ones in the same output.
- Do not repeatedly read unchanged `.lean` files.
- After a failed proof, inspect only the error location and nearby definitions.
- Prefer small proof attempts and verify after each change.
- Do not use verbose flags unless debugging requires them.

## Dependencies

- **Mathlib only.** No other external Lean libraries; the toolchain and Mathlib revision are pinned (`lean-toolchain`, `lake-manifest.json`) and upgraded deliberately, not as a side effect of other work.
- **Survey Mathlib before building new theory.** Record the survey's outcome (what exists, what is missing, at which revision) in the relevant roadmap file, so the decision to build in-project is traceable and re-checkable after upgrades.
- **Prefer Mathlib's general machinery over bespoke constructions** when both can close a goal, even if the bespoke route is locally shorter.

## Branch and PR workflow

- **One branch per unit of work**, cut from up-to-date `main`, named `type/short-slug` matching the commit type.
- **A PR is created for every unit of work**; the full project must build with no `sorry` before the PR is opened.
- **Merging requires an explicit instruction from the user** and passing CI; merges are squash merges with branch deletion, followed by syncing local `main`.

## Commit conventions

- **Format:** [Conventional Commits](https://www.conventionalcommits.org/) — `type(scope): summary`, imperative mood, summary line kept short. Add a body when the "why" needs explanation.
- **Language:** English, regardless of the language used in chat/discussion.
- **Common types:** `feat` (new definition/theorem/proof), `fix` (correction to a definition or proof), `docs` (notes/ or root-level docs only), `refactor`, `chore` (tooling, deps, CI).
- **Scope:** name the affected area, e.g. `roadmap`, `conventions`, or a Lean module/namespace once source files exist.
