import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.BandOccupation
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureOccupation

set_option linter.style.header false

/-!
# Generic transport analysis

Public opt-in package boundary for model-independent analytical utilities used by transport
consumers. It exports angular-harmonic integrals, generic band and zero-temperature occupation,
two-dimensional polar Fourier reduction with physical momentum normalization, and the positive
transport-lifetime datum.

This package contains no concrete Hamiltonian, disorder model, response approximation, or
conductivity benchmark. It is intentionally separate from the root `LeanCondensedMatter.Transport`
umbrella so consumers that only need the core, resolvent, Kubo–Bastin, Středa, or generic disorder
interfaces do not acquire these analytical utilities transitively.

The leaves remain directly importable for low-level consumers that need only one narrow utility;
higher-level consumers spanning several of these utilities should prefer this package boundary.
-/
