import Mathlib.Tactic.DuplicateDecls
import LeanCondensedMatter

/-!
# Advisory duplicate theorem report

After building the project, run:

```sh
lake env lean scripts/ReportDuplicateTheorems.lean
```

Mathlib's duplicate-declaration tool examines the imported environment, including
dependencies. It normalizes the order of independent binders and ignores binder
information and universe levels. Inspect groups under LeanCondensedMatter module
headings for project-related candidates; the report also includes dependency-only
groups.

This is a discovery tool, not a proof of interchangeability. Check universe
constraints, intended public interfaces, simp rules, and consumers before removing
any declaration. The exact project-local duplicate check remains separate.
This file deliberately uses non-module imports, as required by the Mathlib tool.
-/

open Lean Mathlib.Tactic.DuplicateDecls

-- This is an explicit whole-environment offline audit, not a library proof.
set_option maxHeartbeats 0 in
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"
