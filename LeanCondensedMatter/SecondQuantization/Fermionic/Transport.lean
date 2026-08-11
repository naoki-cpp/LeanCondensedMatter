import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StredaOccupation
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StredaCommonKernel
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StaticStredaWardBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FiniteDisorderConductivity

set_option linter.style.header false

/-!
# Fermionic transport adapters

This umbrella contains the finite-lattice fermionic adapters for the generic Středa and transport
theory. The reusable occupation, resolvent, trace, and integration layers live under
`QuantumTheory.Transport`; these modules add only finite Fock-space currents, contacts, Peierls
normalization, and disorder specializations.
-/
