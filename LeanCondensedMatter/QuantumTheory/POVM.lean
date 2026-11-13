import LeanCondensedMatter.QuantumTheory.POVM.Basic
import LeanCondensedMatter.QuantumTheory.POVM.Born

set_option linter.style.header false

/-!
# Public discrete-POVM API

This focused package entry point exposes the countable-outcome POVM and Born-probability API.
POVM semantics are owned by `POVM.Basic` and `POVM.Born`; the density-state implementation
remains upstream. For source files needing a single declaration, import its owning leaf.
-/
