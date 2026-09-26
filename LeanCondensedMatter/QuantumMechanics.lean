import LeanCondensedMatter.QuantumMechanics.SingleParticle

set_option linter.style.header false

/-!
# Quantum mechanics

Concrete first-quantized quantum mechanics. The current API centers on one-particle continuum
Schrödinger mechanics together with generic one-particle current and angular-momentum constructions.

State, thermodynamic, conservation-law, and response abstractions that do not depend on a concrete
first-quantized realization belong upstream in `QuantumTheory`.
-/
