import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ProductDomain
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeHamiltonianLadder
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

Public entry point for the completed fermionic representation: the `ℓ²` occupation space, dense
algebraic core, bounded number/creation/annihilation operators and CAR, maximal diagonal operators
and their analytic properties, free-Hamiltonian domains and ladder relations, finite-dimensional
compatibility, and finite-mode representation truncations.

Thermal states, Gibbs summability and expectations, finite-mode Gibbs convergence, Gibbs
intertwining, thermal ladder packaging, peel/KMS identities, and the completed Bloch--de Dominicis
recursion are owned by `SecondQuantization.Fermionic.Thermal` (with completed-representation
specializations under `SecondQuantization.Fermionic.Thermal.Completed`).

No unbounded operator is coerced into `ContinuousLinearMap`; products involving the completed free
Hamiltonian are stated on its explicit maximal domain.
-/
