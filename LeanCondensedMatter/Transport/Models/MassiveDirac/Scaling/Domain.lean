import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Domain for the massive-Dirac anomalous-Hall scaling problem

This module records the parameter domain used by the universal-scaling roadmap.  It keeps the
model-specific hypotheses in one value, while leaving the generic `Transport` API independent of
the Massive-Dirac realization.  The field `scatteringScale` is the chosen energy scale for the
disorder broadening; later constructions may instantiate it with `ℏ / τ_tr`.

No scaling law is asserted here.  In particular, the ultraviolet cutoff condition only records the
metallic shell used by the finite-cutoff formulas, and `referenceEnergy` is a user-chosen positive
normalization scale rather than an additional physical identification.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Parameters and domain conditions for a normalized Massive-Dirac AHE scaling observable. -/
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
  /-- Positive energy scale used to nondimensionalize the scattering coordinate. -/
  referenceEnergy : ℝ
  /-- Chosen positive scattering/broadening energy scale `γ`. -/
  scatteringScale : ℝ
  hbar_pos : 0 < hbar
  velocity_ne_zero : v ≠ 0
  metallic : |m| < fermiEnergy
  cutoff_nonneg : 0 ≤ pMax
  cutoff_shell : fermiEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2
  disorder_pos : 0 < disorderStrength
  referenceEnergy_pos : 0 < referenceEnergy
  scatteringScale_pos : 0 < scatteringScale
  charge_ne_zero : e ≠ 0

/-- The chosen disorder broadening energy, e.g. `ℏ / τ_tr` for a transport lifetime. -/
def AheScalingParameters.gamma (params : AheScalingParameters) : ℝ :=
  params.scatteringScale

/-- Dimensionless disorder coordinate `x = γ / E_ref`. -/
def AheScalingParameters.dimensionlessScattering (params : AheScalingParameters) : ℝ :=
  params.gamma / params.referenceEnergy

/-- Conductivity normalized in the `e² / h` convention, `σ̂ = (h/e²) σ`, using the
charge and reduced-Planck-constant data of this scaling point. -/
def AheScalingParameters.normalizedConductivity
    (params : AheScalingParameters) (sigma : ℝ) : ℝ :=
  (planckFromReduced params.hbar / params.e ^ 2) * sigma

/-- Complex-valued counterpart of `normalizedConductivity`, used before zero-broadening or other
reality statements have been proved for a physical conductivity component. -/
def AheScalingParameters.normalizedComplexConductivity
    (params : AheScalingParameters) (sigma : ℂ) : ℂ :=
  (((planckFromReduced params.hbar / params.e ^ 2 : ℝ) : ℂ)) * sigma

lemma AheScalingParameters.referenceEnergy_ne_zero (params : AheScalingParameters) :
    params.referenceEnergy ≠ 0 :=
  ne_of_gt params.referenceEnergy_pos

lemma AheScalingParameters.scatteringScale_ne_zero (params : AheScalingParameters) :
    params.scatteringScale ≠ 0 :=
  ne_of_gt params.scatteringScale_pos

lemma AheScalingParameters.charge_sq_ne_zero (params : AheScalingParameters) :
    params.e ^ 2 ≠ 0 :=
  pow_ne_zero 2 params.charge_ne_zero

lemma AheScalingParameters.dimensionlessScattering_pos (params : AheScalingParameters) :
    0 < params.dimensionlessScattering := by
  unfold AheScalingParameters.dimensionlessScattering AheScalingParameters.gamma
  exact div_pos params.scatteringScale_pos params.referenceEnergy_pos

lemma AheScalingParameters.fermiEnergy_pos (params : AheScalingParameters) :
    0 < params.fermiEnergy :=
  lt_of_le_of_lt (abs_nonneg params.m) params.metallic

end

end QuantumTheory.Transport.Models.MassiveDirac
