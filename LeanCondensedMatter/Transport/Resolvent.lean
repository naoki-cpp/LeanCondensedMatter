import LeanCondensedMatter.Transport.Resolvent.Basic
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import LeanCondensedMatter.Transport.Resolvent.DressedEnergyDerivative
import LeanCondensedMatter.Transport.Resolvent.Uniqueness
import LeanCondensedMatter.Analysis.Lorentzian.Kernel

set_option linter.style.header false

/-!
# Transport resolvent API

Public umbrella for dimension-independent retarded/advanced resolvents, the abstract Dyson
self-energy relation, their pure-point spectral action, clean and dressed real-energy derivatives,
uniqueness of side-indexed resolvent candidates, and the reusable scalar Lorentzian pole kernel.

Canonical resolvent implementations live under `Transport/Resolvent/`; the model-independent
Lorentzian kernel is owned by `Analysis/Lorentzian/Kernel.lean`.
-/
