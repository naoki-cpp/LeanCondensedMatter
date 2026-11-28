import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.SmearedField
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnitaryLift
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Generator
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ProductDomain
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeHamiltonianLadder
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation

set_option linter.style.header false

/-!
# Completed fermionic Fock space

Occupation `ℓ²` space and its algebraic core, bounded mode and smeared ladder operators,
CAR, one-particle unitary lifts and generators, maximal diagonal operators, free-Hamiltonian
product domains, and finite-mode compatibility and truncations.
Thermal constructions are provided by `Fermionic.Thermal`.
-/
