import LeanCondensedMatter.Transport.Core.ContinuumMeasure

set_option linter.style.header false

/-!
# Massive-Dirac conductivity normalization

This module owns the scalar normalization shared by physically normalized massive-Dirac
Kubo–Bastin/Středa conductivity consumers. Current vertices already contain the charge `-e`, so the
traced static response receives only the standard `ℏ/(2π)` trace prefactor before the continuum
momentum measure is attached downstream.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Scalar prefactor that converts the canonical traced Bastin/Středa response to a static
conductivity component before the continuum momentum measure is applied. -/
def bastinTraceConductivityPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

end

end QuantumTheory.Transport.Models.MassiveDirac
