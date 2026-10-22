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
`import` in a module makes an imported module's public scope available locally,
not to consumers of the current module. Consumers should import the canonical
owners of the APIs they use directly, rather than depend on incidental transitive
imports. `public import` re-exports the imported module's public scope; reserve it
for a genuine public-signature dependency or an intentional umbrella interface.
A public declaration's type may mention only public names, so not every
`public import` can simply be downgraded to `import`. This distinction supports
narrower interfaces and fewer downstream rebuilds when only private proofs change.

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
- **Use direct ordinary imports by default.** Each consumer imports the modules
  owning the declarations it actually uses; do not re-export dependencies just
  to spare downstream files an explicit import. Use `public import` only when
  the public scope needs an imported declaration to express or elaborate an
  exported signature, or when a designated umbrella intentionally re-exports
  that interface. Prefer the narrowest owner module for either case. Keep
  proof-only imports (including tactics and supporting rewrite lemmas) ordinary.
  If a downstream file loses an accidental transitive dependency, add its
  direct `import` rather than widening the upstream public API.
- **Keep visibility mechanisms distinct.** `public section` publishes this
  file's declarations; it does not re-export ordinary imports. Use `import all`
  or `meta import` only when a concrete private-scope or metaprogramming need
  is demonstrated. Treat broad `@[expose] public section` and temporary
  backward-compatibility options as migration scaffolding, not the final
  visibility policy.
- **Avoid unrelated refactors.** A module-conversion PR should not also
  rename physical concepts, rearrange the architecture, or alter theorem
  meaning. Genuine API improvements follow the normal canonical-ownership
  rules and receive their own focused review.

## Import-boundary example

A theorem module that exports a statement about `Complex.exp` can use
`public import Mathlib.Analysis.Complex.Exponential` for the public name but
ordinary `import Mathlib.Analysis.Complex.Trigonometric` for proof-only facts
such as `Complex.norm_exp`. Callers requiring trigonometric results should
import their Mathlib owner directly, not rely on this theorem module to
re-export them. Conversely, replacing *both* imports with ordinary imports
would make the theorem's public signature invalid.

```lean
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

public section
```

## Migration and verification

1. Establish the supported toolchain/Mathlib baseline and confirm it builds
   in compatibility mode before converting files.
2. Inspect direct imports and in-repository consumers; select an upstream
   pilot file that can legally use a `module` header. Classify each import as
   a public-signature dependency, proof/implementation-only dependency, or
   intentional re-export. Begin with ordinary imports, then promote only the
   imports needed for a valid public interface.
3. Compile the edited module and relevant consumers. If callers relied on
   unintentional re-exports, add direct imports at those use sites. If the
   exported signature needs an imported name, publish the narrowest owner
   dependency. Fix private-name or definitional-equality failures by narrowing
   the API boundary where possible; expand `public` and `@[expose]` only
   with a concrete consumer need.
4. Extend the converted region along dependency edges. At coherent milestones,
   run the existing architecture checks, `lake build --wfail`, lints, and
   no-`sorry` / declaration checks. Verify that public theorem signatures
   and physical assumptions remain correct.
5. When no legacy source files remain, remove `allowNonModules` and assess
   enabling `requiresModuleSystem = true` as an explicit contract for
   downstream importers. Validate the complete library before claiming the
   migration finished.

Review each migration by inspecting the public/private interface, direct
consumer imports, and rebuild impact, not merely whether a `module` header
compiles. Document an actual change to module ownership in the relevant
architecture note.

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
