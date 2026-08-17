import LeanCondensedMatter.QuantumTheory.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergTransport

set_option linter.style.header false

/-!
# One-body conservation-law and transport abstractions

Public umbrella for particle-statistics-independent one-body transport semantics. The algebraic
localized balance law and weak-current abstractions live upstream under `Analysis`; this layer adds
Heisenberg normalization and model-independent transport factorization. Concrete velocity and
conventional-current specializations are owned by `QuantumMechanics.SingleParticle`.
-/
