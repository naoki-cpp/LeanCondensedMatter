---
status: accepted
---

# Keep Lean module visibility explicit

Lean's module system distinguishes public declarations from private implementation
and controls what imports expose to downstream users. Declare the intended API
without exporting proof machinery or unrelated transitive dependencies.

## Imports and declarations

- Consumers import the canonical owner of each API they use. Use ordinary
  `import` for implementation and proof dependencies.
- Use `public import` when an exported signature needs an imported public name
  or when an intentional umbrella re-exports a coherent interface. It is not a
  shortcut for missing direct imports in consumers.
- Use `public section` for declarations intended as public API. Keep local
  proof helpers private; expose definitions with `@[expose]` only when callers
  require their definitional reduction.
- Do not add forwarding modules, duplicate declarations, or compatibility
  aliases merely to bypass visibility errors. Follow the semantic ownership
  rules in [ADR 0002](0002-semantic-ownership.md).

## Repository boundary

The repository currently contains both module-system and non-module Lean files;
`allowNonModules = true` in [Lake](../../lakefile.toml) permits that combination.
This setting does not make non-module files into modules. A module-system file
can import only modules, so conversions must follow actual dependency edges.
Keep the module boundary accurate without claiming full migration.

For a modified module, inspect its imports and exported signatures, compile it
and its consumers, and run the relevant architecture checks. Fix missing
dependencies at their use sites, rather than broadening upstream re-exports.
Preserve theorem meaning and physical assumptions when changing visibility.

See [Lean's module reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
and [project conventions](../conventions.md).
