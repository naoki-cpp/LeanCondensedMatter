import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeneralizedQuantity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ContinuumChargeDensity1D
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ContinuumL2ChargeDensity1D

set_option linter.style.header false

/-!
# Fermionic field interfaces

This narrow layer owns basis-independent fermionic density interfaces and the fermionic `dΓ` bridge
for generalized localized one-body quantities. One-body balance/current semantics live upstream under
`Analysis` and `QuantumTheory`; lattice and Peierls constructions live under `Fermionic.Lattice`,
response/conductivity specializations under `Fermionic.Transport`, and finite toy models under
`Fermionic.Validation`.
-/
