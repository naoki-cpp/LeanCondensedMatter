import LeanCondensedMatter.QuantumTheory.Occupation.Band
import LeanCondensedMatter.QuantumTheory.Occupation.BandFilling
import LeanCondensedMatter.QuantumTheory.Occupation.ZeroTemperature

set_option linter.style.header false

/-!
# Spectral occupation laws

General energy-based occupation laws and their zero-temperature spectral consequences, independent
of transport observables, response approximations, and Fermi-edge integration. This module groups
the occupation-law composition, strict zero-temperature step, and finite-band filling predicates.

Lorentzian Fermi-edge integration remains downstream in `Transport.Analysis.ZeroTemperatureLorentzian`.
-/
