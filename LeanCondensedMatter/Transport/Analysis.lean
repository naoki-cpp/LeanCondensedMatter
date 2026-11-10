import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.BesselRadialMoments
import LeanCondensedMatter.Transport.Analysis.BesselY0Series
import LeanCondensedMatter.Transport.Analysis.BesselY1Series
import LeanCondensedMatter.Transport.Analysis.BesselYFormalWronskian
import LeanCondensedMatter.Transport.Analysis.BesselYFormalCoefficients
import LeanCondensedMatter.Transport.Analysis.BesselYFormalOrderOne
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialPrimitive
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialLimit
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureLorentzian

set_option linter.style.header false

/-!
# Generic transport analysis

Model-independent analytical tools used in transport calculations: angular harmonics,
Fermi-edge formulas, finite-dimensional Fourier geometry,
continuum momentum measures, polar Fourier reduction, finite-cutoff radial Fourier differentiation and first-harmonic primitives,
Bessel radial-moment analysis,
and positive relaxation-time data.

These results make no choice of Hamiltonian, disorder model, response approximation, or
conductivity benchmark.
-/
