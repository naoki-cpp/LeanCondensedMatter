import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Integral1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.FiniteDimensional
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.TotalProbability1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.CurrentRepresentation1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.ElectromagneticWeak1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2.Probability1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Hamiltonian.SelfAdjoint1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Evolution.Stone1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Evolution.RepresentativeContinuity1D

set_option linter.style.header false

/-!
# Quantum mechanics

Public entry point for concrete first-quantized quantum mechanics. The current public realization is
the one-particle continuum Schrödinger stack under `QuantumMechanics.SingleParticle.Continuum`.

This umbrella imports the stable semantic endpoints of the probability, continuity, `L²`, Hamiltonian,
and evolution layers. Their lower implementation stages remain available transitively and directly
importable as leaf modules, but are not enumerated here merely because of development history.

Generic state and response theory remains upstream in `QuantumTheory`. Implementation modules should
continue to import the narrow concrete modules they use rather than this public umbrella.
-/
