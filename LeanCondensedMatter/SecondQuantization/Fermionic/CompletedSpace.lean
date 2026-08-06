import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

The public entry point for the completed fermionic representation.  The initial vertical slice
contains the `ℓ²` occupation representation, the dense algebraic core, and the bounded single-mode
number projection.  Later modules may add bounded CAR operators, partial linear maps for unbounded
Hamiltonians, and trace-class thermal constructions without changing the algebraic Fock API.
-/
