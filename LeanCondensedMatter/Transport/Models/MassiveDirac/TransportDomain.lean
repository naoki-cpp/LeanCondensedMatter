import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Fixed-cutoff metallic Born-Dyson transport domain

This module packages the common parameter domain used by the fixed-cutoff, positive-disorder
zero-broadening boundary theorems.  It deliberately contains neither conductivity normalization
data such as the electric charge nor result-specific regularity conditions such as the real Born
renormalization bound or the ladder determinant hypothesis.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Common fixed-cutoff metallic domain for Born-Dyson zero-broadening transport boundaries. -/
structure FixedCutoffMetallicBornRegime where
  /-- Dirac velocity parameter. -/
  v : ℝ
  /-- Massive-Dirac gap/mass parameter. -/
  m : ℝ
  /-- Probe/Fermi energy at which the response is evaluated. -/
  probeEnergy : ℝ
  /-- Positive scalar-disorder strength. -/
  disorderStrength : ℝ
  /-- Reduced Planck constant used by the transport formulas. -/
  hbar : ℝ
  /-- Ultraviolet radial momentum cutoff. -/
  pMax : ℝ
  /-- The radial integration interval is oriented in the physical direction. -/
  cutoff_nonneg : 0 ≤ pMax
  /-- The velocity enters denominator and radial-change-of-variable formulas nontrivially. -/
  velocity_ne_zero : v ≠ 0
  /-- The momentum-measure normalization is nonzero. -/
  hbar_ne_zero : hbar ≠ 0
  /-- The fixed-disorder boundary is taken at positive scalar disorder strength. -/
  disorder_pos : 0 < disorderStrength
  /-- The probe energy lies in the metallic shell. -/
  metallic : |m| < probeEnergy
  /-- The cutoff contains the metallic shell. -/
  cutoff_shell : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2

end

end QuantumTheory.Transport.Models.MassiveDirac
