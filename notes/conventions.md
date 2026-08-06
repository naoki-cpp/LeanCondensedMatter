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
- **Create parallel files only for semantically distinct APIs.** When a generalization subsumes an older construction, move the canonical declaration upstream and migrate callers instead of retaining a specialized copy merely for compatibility.
- **Documentation describes the current repository.** Update architecture notes and roadmaps when the current design, constraints, or remaining work changes. Do not append completed-work logs to permanent documentation.

## Refactoring and compatibility

- **The current canonical API is the source of truth.** Outside the exact scope of an active pull request, refactors do not preserve backward compatibility unless the user explicitly requires it for the current task.
- **Inspect active pull requests before editing.** Avoid files, declarations, and architectural decisions currently being changed elsewhere. Unrelated old APIs and paths receive no compatibility protection.
- **Prefer complete breaking migrations.** Rename, move, merge, or delete declarations and modules when doing so yields a clearer ownership boundary, dependency direction, or public API. Migrate all in-repository callers in the same pull request.
- **Do not add compatibility layers by default.** Remove obsolete aliases, forwarding theorems, forwarding modules, duplicate instances, duplicate re-exports, old import paths, and specialized wrappers around canonical generic declarations. Do not replace them with deprecation aliases or forwarding imports.
- **Preserve mathematics, not historical packaging.** A distinct representation, theorem, or physical construction remains when it has independent semantic value. A module or declaration whose only purpose is to preserve an older name, path, layering decision, or proof organization should be removed or folded into its canonical owner.
- **Move general facts upstream.** When a statistics-specific or physics-specific declaration is only a parameter specialization of a general result, use the general declaration directly. If genuinely reusable infrastructure is missing, add it at the most general layer rather than restoring a downstream wrapper.
- **Keep proof helpers private.** Public declarations should express reusable mathematical or physical content. Intermediate uniqueness lemmas, transport steps, and basis calculations used by one proof should be private or local unless an independent caller exists.
- **Delete historical prose during refactors.** Module documentation and permanent notes should state the present model, API, assumptions, dependency boundary, and unresolved limitations. Remove issue and PR numbers, phase or slice labels, migration instructions, completed roadmaps, former-path inventories, and prose whose only content is what used to exist.
- **Retain design rationale only when it constrains current work.** A past decision belongs in permanent documentation only when understanding it is necessary to use, extend, or safely modify the current implementation.
- **Regression checks enforce invariants, not archaeology.** Prefer checks for dependency direction, namespace ownership, canonical imports, or forbidden classes of compatibility layers. Avoid indefinitely enumerating every deleted file, declaration, or import path when a structural invariant can prevent the same regression.
- **Measure refactors by the resulting structure.** Line reduction is useful but secondary. The primary test is whether the repository has fewer competing APIs, clearer ownership, narrower imports, less public proof machinery, and documentation that matches the code now present.

## Proof style

General cautions distilled from past sessions; detailed incident records live in `caveats.md`.

- **Abbreviations made with `have`/`haveI` are opaque.** They are not definitionally equal to the term they abbreviate. When a later step needs to unfold back to the original term, use `let`/`set`, or repeat the term at each use site.
- **Do not reindex a dependent `Sigma` index type through an `Equiv`.** Cast-based equivalences on dependent types risk genuine kernel timeouts even when they type-check. Reindex only the (non-dependent) base type, or split the sum into base and fiber parts instead.
- **Take analytic side conditions as explicit hypotheses.** When a definition needs compactness, summability, non-vanishing, or similar facts that do not follow from the ambient structure, accept them as arguments rather than deriving them — unless the derivation is itself a stated target.
- **Never guess a Mathlib lemma name.** If unsure a lemma exists or what it's called, find it first
  with `exact?`, `apply?`, `#find`, Loogle, or LeanSearch — do not write a plausible-sounding name
  and hope it compiles. Check the found lemma's exact signature with `#check` before using it.
- **Search Mathlib by compiling, not only by text.** When a lemma or instance is hard to locate by name, write a scratch file probing with `#check`/`#synth`/`exact?` and build it; delete the file afterwards.
- **Never leave search scaffolding or `sorry` in the final result.** `#check`/`exact?`/`#find` calls and any placeholder `sorry` are for the search process only; remove them (and delete scratch files) before the change is considered done.
- **Generalize canonically.** Preserve an older specialized declaration only when it expresses a distinct theorem or usable abstraction; otherwise replace it with the general declaration and migrate callers.
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
- **Do not build after a docstring/comment-only change.** If a diff touches only `/-!  -/`/`/-- -/`
  comments (no code, no `omit`/`variable`/import changes), skip `lake build` entirely — check with
  a quick read for syntax sanity instead. This also applies to `notes/`-only changes.
- **Add regression protection after implementation.** Once the completed implementation reveals the
  stable invariant that must not regress, add the narrowest practical automated check before the work
  is declared complete. Prefer theorem- or type-level enforcement; use targeted scripts and CI for
  repository structure, dependency direction, forbidden compatibility layers, or other cross-file
  constraints that Lean does not directly express. Avoid redundant or comment-sensitive grep rules.

## Dependencies

- **Mathlib only.** No other external Lean libraries; the toolchain and Mathlib revision are pinned (`lean-toolchain`, `lake-manifest.json`) and upgraded deliberately, not as a side effect of other work.
- **Survey Mathlib before building new theory.** Record the current survey outcome and the resulting design constraint in the relevant architecture note or active roadmap so it can be re-checked after upgrades; do not preserve a chronological search log.
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
