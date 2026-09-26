import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Domain for the massive-Dirac anomalous-Hall scaling problem

This module records the parameter domain used by the universal-scaling roadmap.  It keeps the
model-specific hypotheses in one value, while leaving the generic `Transport` API independent of
the Massive-Dirac realization. Scaling-only coordinates are kept in a separate value so that
physical transport results do not require them.

No scaling law is asserted here. In particular, the ultraviolet cutoff condition only records the
metallic shell used by the finite-cutoff formulas.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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

/-- Scaling-only coordinates for the massive-Dirac AHE roadmap.

These coordinates are independent of the physical transport point. The longitudinal benchmark and
normalized conductivity pair therefore do not require them. -/
structure AheScalingCoordinate where
  /-- Positive energy scale used to nondimensionalize the scattering coordinate. -/
  referenceEnergy : ℝ
  /-- Chosen positive scattering/broadening energy scale `γ`. -/
  scatteringScale : ℝ
  referenceEnergy_pos : 0 < referenceEnergy
  scatteringScale_pos : 0 < scatteringScale

/-- The chosen disorder broadening energy, e.g. `ℏ / τ_tr` for a transport lifetime. -/
def AheScalingCoordinate.gamma (coordinate : AheScalingCoordinate) : ℝ :=
  coordinate.scatteringScale

/-- Dimensionless disorder coordinate `x = γ / E_ref`. -/
def AheScalingCoordinate.dimensionlessScattering (coordinate : AheScalingCoordinate) : ℝ :=
  coordinate.gamma / coordinate.referenceEnergy

/-- Conductivity normalized in the `e² / h` convention, `σ̂ = (h/e²) σ`, using the
charge and reduced-Planck-constant data of this physical transport point. -/
def AheScalingParameters.normalizedConductivity
    (params : AheScalingParameters) (sigma : ℝ) : ℝ :=
  (planckFromReduced params.hbar / params.e ^ 2) * sigma

lemma AheScalingCoordinate.referenceEnergy_ne_zero (coordinate : AheScalingCoordinate) :
    coordinate.referenceEnergy ≠ 0 :=
  ne_of_gt coordinate.referenceEnergy_pos

lemma AheScalingCoordinate.scatteringScale_ne_zero (coordinate : AheScalingCoordinate) :
    coordinate.scatteringScale ≠ 0 :=
  ne_of_gt coordinate.scatteringScale_pos

lemma AheScalingParameters.charge_sq_ne_zero (params : AheScalingParameters) :
    params.e ^ 2 ≠ 0 :=
  pow_ne_zero 2 params.charge_ne_zero

lemma AheScalingCoordinate.dimensionlessScattering_pos (coordinate : AheScalingCoordinate) :
    0 < coordinate.dimensionlessScattering := by
  unfold AheScalingCoordinate.dimensionlessScattering AheScalingCoordinate.gamma
  exact div_pos coordinate.scatteringScale_pos coordinate.referenceEnergy_pos

lemma AheScalingParameters.fermiEnergy_pos (params : AheScalingParameters) :
    0 < params.fermiEnergy :=
  lt_of_le_of_lt (abs_nonneg params.m) params.metallic

end

end QuantumTheory.Transport.Models.MassiveDirac
