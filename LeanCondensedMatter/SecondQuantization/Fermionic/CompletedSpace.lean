import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

The public entry point for the completed fermionic representation. The current slice contains the
`ℓ²` occupation representation, the dense algebraic core, the bounded single-mode number
projection, and the occupation-toggle equivalence used to construct bounded CAR operators.

Later modules may add the completed creation and annihilation maps, partial linear maps for
unbounded Hamiltonians, and trace-class thermal constructions without changing the algebraic Fock
API.
-/
