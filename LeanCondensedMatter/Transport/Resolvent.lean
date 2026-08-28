import LeanCondensedMatter.Transport.Resolvent.Basic
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import LeanCondensedMatter.Transport.Analysis.LorentzianKernel

set_option linter.style.header false

/-!
# Transport resolvent API

Public umbrella for dimension-independent retarded/advanced resolvents, the abstract Dyson
self-energy relation, their pure-point spectral action, real-energy derivatives, and the reusable
scalar Lorentzian pole kernel.

Canonical implementations live under `Transport/Resolvent/` and `Transport/Analysis/`.
-/
