import LeanCondensedMatter.QuantumMechanics.SingleParticle

set_option linter.style.header false

/-!
# Quantum mechanics

Public entry point for concrete first-quantized quantum mechanics. The current public realization is
the one-particle continuum Schrödinger stack under `QuantumMechanics.SingleParticle.Continuum`, along
with the stable generic one-particle current representation endpoints.

The `SingleParticle` routing module collects the stable semantic endpoints of the probability,
continuity, `L²`, Hamiltonian, and evolution layers. Their lower implementation stages remain
available transitively and directly importable as leaf modules, but are not enumerated here merely
because of development history.

Generic state and response theory remains upstream in `QuantumTheory`. Implementation modules should
continue to import the narrow concrete modules they use rather than this public umbrella.
-/
