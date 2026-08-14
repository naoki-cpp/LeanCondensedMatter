import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.CurrentRepresentation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity.ConventionalCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ContinuumChargeDensity1D
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ContinuumL2ChargeDensity1D

set_option linter.style.header false

/-!
# Fermionic field interfaces

This narrow layer owns basis-independent fermionic field interfaces that are neither lattice-model
data nor transport response. The algebraic Fock core lives under `Fermionic.Algebra`, lattice and
Peierls constructions under `Fermionic.Lattice`, response/conductivity specializations under
`Fermionic.Transport`, and finite toy models under `Fermionic.Validation`.
-/
