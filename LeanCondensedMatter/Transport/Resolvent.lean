import LeanCondensedMatter.Transport.Resolvent.Basic
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import LeanCondensedMatter.Transport.Resolvent.Uniqueness

set_option linter.style.header false

/-!
# Transport resolvent API

Public umbrella for dimension-independent retarded/advanced resolvents, the abstract Dyson
self-energy relation, their pure-point spectral action, clean real-energy derivatives, and uniqueness
of side-indexed resolvent candidates.

Energy derivatives of supplied dressed Green families are an opt-in calculus module under
`Transport.Resolvent.DressedEnergyDerivative`; they are not part of the core resolvent umbrella.
Canonical resolvent implementations live under `Transport/Resolvent/`; representation-independent
analysis primitives such as Lorentzian kernels remain under `Analysis/`.
-/
