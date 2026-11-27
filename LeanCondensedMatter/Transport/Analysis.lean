import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureLorentzian

set_option linter.style.header false

/-!
# Generic transport analysis

Model-independent analytical tools used in transport calculations: angular harmonics,
Fermi-edge formulas, finite-dimensional Fourier geometry,
continuum momentum measures, physical polar Fourier reduction, and positive relaxation-time data.
Radial Fourier differentiation, primitives, and improper limits are opt-in mathematical APIs under
`LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels`.

These results make no choice of Hamiltonian, disorder model, response approximation, or
conductivity benchmark.
-/
