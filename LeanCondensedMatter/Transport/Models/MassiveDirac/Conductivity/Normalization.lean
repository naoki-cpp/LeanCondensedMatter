import LeanCondensedMatter.Transport.Core.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac conductivity normalization

This module owns scalar normalizations shared by physically normalized massive-Dirac
Kubo–Bastin/Středa conductivity consumers. Current vertices already contain the charge `-e`, so the
traced static response receives only the standard `ℏ/(2π)` trace prefactor before the continuum
momentum measure is attached. The combined finite-dimensional Středa normalization is named here so
all momentum-space conductivity consumers use the same physical-momentum normalization boundary.

`bastinTraceConductivityPrefactor` is also the canonical downstream factor for a response whose
construction already contains its physical momentum measure, such as the crossed real-space Fourier
blocks. Such consumers must not use the combined normalization and attach the measure a second time.
This module also owns the shared conversion `h = 2πℏ` used when closed-form conductivities are written
in `e²/h` units.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Planck's constant expressed through the reduced Planck constant, `h = 2πℏ`. -/
def planckFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

/-- Scalar prefactor that converts the canonical traced Bastin/Středa response to a static
conductivity component before the continuum momentum measure is applied. When the response already
contains the physical momentum measure, this is the complete remaining normalization. -/
def bastinTraceConductivityPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Combined normalization for a traced Bastin/Středa response integrated with the two-dimensional
physical-momentum continuum measure. -/
def bastinStredaConductivityNormalization (hbar : ℝ) : ℝ :=
  bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar

/-- The combined Bastin/Středa normalization consists of exactly one trace prefactor and exactly one
physical-momentum measure factor. -/
theorem bastinStredaConductivityNormalization_eq_trace_mul_momentumMeasure
    (hbar : ℝ) :
    bastinStredaConductivityNormalization hbar =
      bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar := by
  rfl

end

end QuantumTheory.Transport.Models.MassiveDirac
