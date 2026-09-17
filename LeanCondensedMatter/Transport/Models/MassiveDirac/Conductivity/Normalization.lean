import LeanCondensedMatter.Transport.Core.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac conductivity normalization

This module owns scalar normalizations shared by physically normalized massive-Dirac
Kubo–Bastin/Středa conductivity consumers. Current vertices already contain the charge `-e`, so a
traced static response receives the standard `ℏ/(2π)` trace prefactor before any continuum momentum
measure is attached.

Momentum-space responses use `bastinStredaConductivityNormalization`, which includes exactly one
physical-momentum measure. Responses whose construction already contains that measure, such as the
crossed real-space Fourier blocks, use only `bastinTraceConductivityPrefactor`. The module also owns
`h = 2πℏ` for closed forms written in `e²/h` units.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Planck's constant expressed through the reduced Planck constant, `h = 2πℏ`. -/
def planckFromReduced (hbar : ℝ) : ℝ :=
  2 * Real.pi * hbar

/-- Trace normalization before a physical momentum measure is attached; it is also the complete
remaining normalization when that measure is already present upstream. -/
def bastinTraceConductivityPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Combined normalization for a traced Bastin/Středa response integrated with the two-dimensional
physical-momentum continuum measure. -/
def bastinStredaConductivityNormalization (hbar : ℝ) : ℝ :=
  bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar

end

end QuantumTheory.Transport.Models.MassiveDirac
