---
status: accepted
---

# Migrate to Lean's module system incrementally

LeanCondensedMatter will adopt Lean's module system as its long-term source and
API boundary. A toolchain/Mathlib upgrade and a repository-wide module-system
migration are separate changes: the former must not silently force the latter.

## Context

Lean modules distinguish public names, private implementation details, and
whether the body of a public definition can be unfolded by importers. Ordinary
`import` in a module makes an imported module's public scope available locally;
`public import` also re-exports it. This supports narrower imports, more stable
interfaces, and fewer downstream rebuilds when only private proofs change.

Modern Mathlib declares that its API is designed for the module system.
LeanCondensedMatter still has source files without a `module` header. Lake's
`allowNonModules = true` is an explicit compatibility choice that suppresses
the resulting import warnings; it **does not convert** those source files.
In particular, a module-system file may only import other modules, so migration
must respect the actual import dependency graph.

## Decision

- **Decouple upgrades from migration.** Keep the Lean and Mathlib pins coherent
  first. Permit `allowNonModules = true` during the transitional mixed state,
  retaining `--wfail` and other checks. Remove that setting when the project
  has completed its migration; do not treat it as permanent architecture.
- **Migrate in dependency order.** Start with small upstream source files whose
  imports already support the module system, then migrate their consumers.
  Prefer general `Analysis` and `Combinatorics` dependencies before their
  `QuantumTheory`, `SecondQuantization`, and model consumers when the
  actual import graph permits it. Do not assume directory order alone is a
  valid migration order.
- **Expose semantic APIs, not proof plumbing.** Make independently reusable
  declarations public and keep file-local helpers private. Preserve the
  established mathematical statements, hypotheses, physical conventions,
  and canonical ownership. Do not add forwarding declarations or
  compatibility-only modules to work around visibility errors.
- **Control definitional transparency.** A public definition is not
  necessarily unfoldable by importers. Use `@[expose]` only when downstream
  definitional reduction is an intentional interface; otherwise supply
  canonical public equations or theorems and refactor consumers to use them.
  Do not expose proof internals merely to make a tactic succeed.
- **Keep imports narrow.** Use ordinary `import` by default and
  `public import` only for intentional re-exporting. Use `import all`
  or `meta import` only when the relevant private or metaprogramming
  dependency is demonstrated. For theorem modules, keep imports needed to
  form or elaborate exported statements public, but leave proof-only helpers
  as ordinary imports; verify actual downstream consumers before narrowing a
  public import. Treat broad `@[expose] public section` and temporary
  backward-compatibility options as migration scaffolding, not the final
  visibility policy.
- **Avoid unrelated refactors.** A module-conversion PR should not also
  rename physical concepts, rearrange the architecture, or alter theorem
  meaning. Genuine API improvements follow the normal canonical-ownership
  rules and receive their own focused review.

## Migration and verification

1. Establish the supported toolchain/Mathlib baseline and confirm it builds
   in compatibility mode before converting files.
2. Inspect direct imports and in-repository consumers; select an upstream
   pilot file that can legally use a `module` header. Convert its imports and
   identify the declarations genuinely needed by downstream clients.
3. Compile the edited module and relevant consumers. Fix private-name or
   definitional-equality failures by narrowing the API boundary where possible;
   expand `public` and `@[expose]` only with a concrete consumer need.
4. Extend the converted region along dependency edges. At coherent milestones,
   run the existing architecture checks, `lake build --wfail`, lints, and
   no-`sorry` / declaration checks. Verify that public theorem signatures
   and physical assumptions remain correct.
5. When no legacy source files remain, remove `allowNonModules` and assess
   enabling `requiresModuleSystem = true` as an explicit contract for
   downstream importers. Validate the complete library before claiming the
   migration finished.

Review each migration by inspecting the public/private interface and the
rebuild impact, not merely whether a `module` header compiles. Document an
actual change to module ownership in the relevant architecture note.

## Alternatives and consequences

Converting every file in the Mathlib-upgrade PR would combine independent
risks and make failures hard to isolate. Leaving the compatibility switch
indefinitely would forgo the explicit API and rebuild benefits. Blanket
`public` / `@[expose]` declarations would get code compiling quickly but
freeze unnecessary implementation details into the exported interface.

Incremental conversion costs additional dependency analysis and focused
consumer builds, but permits transparent review of each visibility boundary.
This decision extends [ADR 0001](0001-lean-and-mathlib.md) on deliberate
Mathlib upgrades and [ADR 0002](0002-semantic-ownership.md) on canonical
semantic ownership; implementation is progressing through focused, CI-verified changes.

References: [Lean reference manual — Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
and [Lake configuration](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
