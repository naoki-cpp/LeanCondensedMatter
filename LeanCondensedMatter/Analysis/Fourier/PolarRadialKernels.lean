import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.HigherHarmonics
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.AngularReduction

set_option linter.style.header false

/-!
# Dimensionless polar Fourier–Bessel kernels

This module re-exports the higher Fourier harmonics, Bessel bridges,
angular integration and shift formulas. The core definitions, zeroth-order
Bessel bridge, and angular differentiation are available as separate modules.

This mathematical analysis layer is independent of physical momentum
normalizations and transport models; the physical adapter is
`Transport.Analysis.PolarFourier`.
-/
