import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

The public entry point for the completed fermionic representation. The current slice contains the
`ℓ²` occupation representation, the dense algebraic core, the bounded single-mode number
projection, the occupation-toggle equivalence, bounded creation and annihilation maps, their
occupation-basis action, agreement with the algebraic ladder operators on the finite-support core,
and the canonical anticommutation relations lifted to the completion by density and continuity.
It also exposes domain-carrying diagonal partial operators, including the completed free Hamiltonian
and total-number operator on their natural weighted `ℓ²` domains. Maximal diagonal multiplication
operators are densely defined and closed, their adjoints are the conjugate-weight diagonal
operators, and conjugation-fixed weights are self-adjoint; in particular this applies to the free
Hamiltonian and total-number operator.

Trace-class thermal constructions and later infinite-mode thermodynamics remain subsequent analytic
work.
-/
