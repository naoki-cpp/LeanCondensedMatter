import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

The public entry point for the completed fermionic representation. The current slice contains the
`ℓ²` occupation representation, the dense algebraic core, the bounded single-mode number
projection, the occupation-toggle equivalence, and its continuous linear isometric lift.

Completed creation and annihilation maps are built from the toggle, the occupation projections, and
the fermionic phase. Partial linear maps for unbounded Hamiltonians and trace-class thermal
constructions remain later slices.
-/
