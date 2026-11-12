import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Domain for the massive-Dirac anomalous-Hall scaling problem

This module packages the model-specific parameter domain used for anomalous-Hall scaling statements
without adding those assumptions to the generic `Transport` API. Scaling coordinates are stored
separately from the physical transport point so conductivity results need only the hypotheses they
actually use.

No scaling law is asserted here. In particular, the ultraviolet cutoff condition records the
metallic shell used by the finite-cutoff formulas.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- Minimal physical domain for the Born-RTA longitudinal benchmark.

This point intentionally has no ultraviolet cutoff or scaling-coordinate data. -/
structure AheBornRtaParameters where
  /-- Electric charge parameter retained for the transport normalization interface. -/
  e : ℝ
  /-- Reduced Planck constant used by the Massive-Dirac transport formulas. -/
  hbar : ℝ
  /-- Dirac velocity parameter. -/
  v : ℝ
  /-- Massive-Dirac gap/mass parameter. -/
  m : ℝ
  /-- Fermi energy in the strict metallic regime. -/
  fermiEnergy : ℝ
  /-- Positive scalar-disorder strength `W`. -/
  disorderStrength : ℝ
  hbar_pos : 0 < hbar
  velocity_ne_zero : v ≠ 0
  metallic : |m| < fermiEnergy
  disorder_pos : 0 < disorderStrength

/-- Parameters and domain conditions for a finite-cutoff Massive-Dirac AHE observable.

This is the physical transport point. Scaling-only coordinates live in `AheScalingCoordinate` and
are not required by the conductivity pair or the longitudinal benchmark. -/
structure AheScalingParameters where
  /-- Electric charge entering the conductivity normalization. -/
  e : ℝ
  /-- Reduced Planck constant used by the Massive-Dirac transport formulas. -/
  hbar : ℝ
  /-- Dirac velocity parameter. -/
  v : ℝ
  /-- Massive-Dirac gap/mass parameter. -/
  m : ℝ
  /-- Fermi energy in the strict metallic regime. -/
  fermiEnergy : ℝ
  /-- Ultraviolet radial momentum cutoff. -/
  pMax : ℝ
  /-- Positive scalar-disorder strength `W`. -/
  disorderStrength : ℝ
  hbar_pos : 0 < hbar
  velocity_ne_zero : v ≠ 0
  metallic : |m| < fermiEnergy
  cutoff_nonneg : 0 ≤ pMax
  cutoff_shell : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2
  disorder_pos : 0 < disorderStrength
  charge_ne_zero : e ≠ 0

/-- Auxiliary coordinates used to state dimensionless massive-Dirac AHE scaling relations.

These coordinates are independent of the physical transport point, so longitudinal benchmarks and
normalized conductivity pairs do not require them. -/
structure AheScalingCoordinate where
  /-- Positive energy scale used to nondimensionalize the scattering coordinate. -/
  referenceEnergy : ℝ
  /-- Chosen positive scattering/broadening energy scale `γ`. -/
  scatteringScale : ℝ
  referenceEnergy_pos : 0 < referenceEnergy
  scatteringScale_pos : 0 < scatteringScale

/-- Dimensionless disorder coordinate `x = γ / E_ref`. -/
def AheScalingCoordinate.dimensionlessScattering (coordinate : AheScalingCoordinate) : ℝ :=
  coordinate.scatteringScale / coordinate.referenceEnergy

lemma AheScalingCoordinate.dimensionlessScattering_pos (coordinate : AheScalingCoordinate) :
    0 < coordinate.dimensionlessScattering := by
  unfold AheScalingCoordinate.dimensionlessScattering
  exact div_pos coordinate.scatteringScale_pos coordinate.referenceEnergy_pos

end

end QuantumTheory.Models.MassiveDirac
