import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.BandOccupation
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Analysis.RelaxationTime
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureBandFilling
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureLorentzian
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureOccupation

set_option linter.style.header false

/-!
# Generic transport analysis

Model-independent analytical tools used in transport calculations: angular harmonics, band
occupation, zero-temperature filling and Fermi-edge formulas, continuum momentum measures, polar
Fourier reduction, and positive relaxation-time data.

These results make no choice of Hamiltonian, disorder model, response approximation, or
conductivity benchmark.
-/
