import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ProductDomain
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeHamiltonianLadder
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnboundedExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbsSummability
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteThermalCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.GibbsModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.GibbsModeTruncationExpectation

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

Public entry point for the completed fermionic representation: the `ℓ²` occupation space, dense
algebraic core, bounded number/creation/annihilation operators and CAR, maximal diagonal operators
and their analytic properties, free-Hamiltonian domains and ladder relations, finite-dimensional
compatibility, and finite-mode representation truncations.

Thermal states, Gibbs intertwining, thermal ladder packaging, peel/KMS identities, and the completed
Bloch--de Dominicis recursion are owned by `SecondQuantization.Fermionic.Thermal.Completed` and are
exported through `SecondQuantization.Fermionic.Thermal`. Gibbs-specific summability and truncation
modules that have not yet migrated remain here temporarily and are handled by the subsequent
thermal-ownership phase.

No unbounded operator is coerced into `ContinuousLinearMap`; products involving the completed free
Hamiltonian are stated on its explicit maximal domain.
-/
