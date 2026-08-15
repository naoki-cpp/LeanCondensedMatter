import LeanCondensedMatter.QuantumTheory.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergTransport
import LeanCondensedMatter.QuantumTheory.ConservationLaw.ConventionalCurrent
import LeanCondensedMatter.QuantumTheory.ConservationLaw.SchwartzCurrent1D
import LeanCondensedMatter.QuantumTheory.ConservationLaw.SchwartzSpinCurrent1D

set_option linter.style.header false

/-!
# One-body conservation-law and current specializations

Public umbrella for particle-statistics-independent one-body transport semantics. The algebraic
localized balance law and weak-current abstractions live upstream under `Analysis`; this layer adds
Heisenberg normalization, conventional-current specialization, and concrete Schwartz realizations.
-/
