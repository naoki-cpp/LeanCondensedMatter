import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import LeanCondensedMatter.Transport.Analysis.BandOccupation

set_option linter.style.header false

/-!
# Spectral occupation of the massive-Dirac bands

This file connects the concrete two-band massive-Dirac spectrum to the generic transport
band-occupation layer. The spectral labels remain `lower` and `upper`; semiconductor-specific
`valence` / `conduction` terminology is downstream interpretation rather than primitive data.

The radial specialization owns the metallic Fermi radius and the Fermi-surface specialization of
the radial group-velocity average because both are consequences of the spectrum and its occupation,
not of a particular response representation or relaxation model.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Massive-Dirac band energy regarded as a function on two-dimensional physical momentum. -/
def bandEnergyOnMomentum (v m : ℝ) (band : Band) (p : ℝ × ℝ) : ℝ :=
  bandEnergy band v m p.1 p.2

/-- Massive-Dirac band energy on the radial momentum coordinate used by the isotropic transport
reduction. Downstream Fermi-surface statements restrict this coordinate to the nonnegative axis. -/
def radialBandEnergy (v m : ℝ) (band : Band) (p : ℝ) : ℝ :=
  bandEnergy band v m p 0

/-- Any massive-Dirac lower band is filled when the Fermi energy is positive. -/
theorem lowerBand_isFilled_of_pos_fermiEnergy
    (v m fermiEnergy : ℝ) (hfermi : 0 < fermiEnergy) :
    IsFilledBand (bandEnergyOnMomentum v m) fermiEnergy .lower := by
  intro p
  simp only [bandEnergyOnMomentum, bandEnergy_lower]
  have henergy : 0 ≤ energy v m p.1 p.2 := Real.sqrt_nonneg _
  linarith

/-- The upper-band zero-temperature occupied region is exactly the region where the positive Dirac
energy lies below the Fermi energy. -/
theorem mem_upperBand_occupiedRegion_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    p ∈ occupiedRegion (bandEnergyOnMomentum v m) fermiEnergy .upper ↔
      energy v m p.1 p.2 < fermiEnergy := by
  simp [occupiedRegion, bandEnergyOnMomentum]

/-- The upper-band Fermi surface is the level set of the positive Dirac energy. -/
theorem mem_upperBand_fermiSurface_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    p ∈ fermiSurface (bandEnergyOnMomentum v m) fermiEnergy .upper ↔
      energy v m p.1 p.2 = fermiEnergy := by
  simp [fermiSurface, bandEnergyOnMomentum]

/-- Every lower-band state has unit zero-temperature occupation at positive Fermi energy. -/
theorem lowerBand_zeroTemperatureOccupation_eq_one
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) (hfermi : 0 < fermiEnergy) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
        (bandEnergyOnMomentum v m) .lower p = 1 :=
  bandStateOccupation_zeroTemperature_eq_one_of_isFilledBand
    (bandEnergyOnMomentum v m) fermiEnergy .lower
    (lowerBand_isFilled_of_pos_fermiEnergy v m fermiEnergy hfermi) p

/-- Upper-band zero-temperature occupation is one exactly below the positive-energy Fermi surface. -/
theorem upperBand_zeroTemperatureOccupation_eq_one_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
        (bandEnergyOnMomentum v m) .upper p = 1 ↔
      energy v m p.1 p.2 < fermiEnergy := by
  rw [bandStateOccupation_zeroTemperature_eq_one_iff]
  simp [bandEnergyOnMomentum]

/-- The positive massive-Dirac radial energy is injective on nonnegative momentum when `v ≠ 0`. -/
theorem energy_radial_eq_imp_eq_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (henergy : energy v m p 0 = energy v m q 0) :
    p = q := by
  have hsquare := congrArg (fun x : ℝ => x ^ 2) henergy
  rw [energy_sq v m p 0, energy_sq v m q 0] at hsquare
  unfold energySq at hsquare
  norm_num at hsquare
  have hpqSq : p ^ 2 = q ^ 2 := hsquare.resolve_right hv
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpqSq with hpq | hpq
  · exact hpq
  · nlinarith

/-- Either massive-Dirac band energy is injective on the nonnegative radial axis when `v ≠ 0`. -/
theorem bandEnergy_radial_eq_imp_eq_of_nonneg
    (band : Band) (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (henergy : bandEnergy band v m p 0 = bandEnergy band v m q 0) :
    p = q := by
  apply energy_radial_eq_imp_eq_of_nonneg v m p q hv hp hq
  cases band <;> simpa [bandEnergy] using henergy

/-- Metallic upper-band Fermi radius for the massive-Dirac dispersion,
`p_F = sqrt(ε_F² - m²) / |v|`. -/
def metallicFermiRadius (v m fermiEnergy : ℝ) : ℝ :=
  Real.sqrt (fermiEnergy ^ 2 - m ^ 2) / |v|

/-- The expression used for the metallic Fermi radius is always nonnegative. -/
theorem metallicFermiRadius_nonneg
    (v m fermiEnergy : ℝ) :
    0 ≤ metallicFermiRadius v m fermiEnergy := by
  unfold metallicFermiRadius
  exact div_nonneg (Real.sqrt_nonneg _) (abs_nonneg v)

/-- Squaring the explicit metallic Fermi radius removes the square root and absolute value whenever
the Fermi energy lies at or above the mass magnitude. -/
theorem metallicFermiRadius_sq
    (v m fermiEnergy : ℝ) (hmF : |m| ≤ fermiEnergy) :
    metallicFermiRadius v m fermiEnergy ^ 2 =
      (fermiEnergy ^ 2 - m ^ 2) / v ^ 2 := by
  unfold metallicFermiRadius
  have hplus : 0 ≤ fermiEnergy + |m| :=
    add_nonneg ((abs_nonneg m).trans hmF) (abs_nonneg m)
  have hprod : 0 ≤ (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_nonneg (sub_nonneg.mpr hmF) hplus
  have hrad : 0 ≤ fermiEnergy ^ 2 - m ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  rw [div_pow, Real.sq_sqrt hrad]
  simp [sq_abs]

/-- The positive Dirac energy at the metallic Fermi radius is exactly `ε_F` whenever
`|m| ≤ ε_F`. -/
theorem energy_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0) (hmF : |m| ≤ fermiEnergy) :
    energy v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy := by
  have hfermiNonneg : 0 ≤ fermiEnergy := (abs_nonneg m).trans hmF
  have hsq :
      energy v m (metallicFermiRadius v m fermiEnergy) 0 ^ 2 =
        fermiEnergy ^ 2 := by
    rw [energy_sq]
    unfold energySq
    norm_num
    rw [metallicFermiRadius_sq v m fermiEnergy hmF]
    field_simp [pow_ne_zero 2 hv]
    ring
  have henergyNonneg :
      0 ≤ energy v m (metallicFermiRadius v m fermiEnergy) 0 :=
    Real.sqrt_nonneg _
  nlinarith

/-- At the occupation-derived metallic Fermi radius, the squared radial energy derivative has the
standard massive-Dirac Fermi-surface form
`v^2 * (1 - m^2 / epsilon_F^2)`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hfermi : fermiEnergy ≠ 0) :
    radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) := by
  unfold radialEnergyDerivative
  rw [energy_metallicFermiRadius v m fermiEnergy hv hmF]
  rw [div_pow, mul_pow,
    metallicFermiRadius_sq v m fermiEnergy hmF]
  field_simp [hfermi, hv]

/-- In the strictly metallic regime `|m| < epsilon_F`, the squared Fermi-surface radial derivative
is strictly positive when `v ≠ 0`. -/
theorem radialEnergyDerivative_sq_metallicFermiRadius_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    0 < radialEnergyDerivative v m (metallicFermiRadius v m fermiEnergy) ^ 2 := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  rw [radialEnergyDerivative_sq_metallicFermiRadius
    v m fermiEnergy hv hmF.le hfermiNe]
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_pos hfermiPos
  have hplus : 0 < fermiEnergy + |m| :=
    add_pos_of_pos_of_nonneg hfermiPos (abs_nonneg m)
  have hprod : 0 < (fermiEnergy - |m|) * (fermiEnergy + |m|) :=
    mul_pos (sub_pos.mpr hmF) hplus
  have hmSqLt : m ^ 2 < fermiEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith
  have hratio : m ^ 2 / fermiEnergy ^ 2 < 1 := by
    exact (div_lt_one hfermiSq).2 hmSqLt
  positivity

/-- The upper-band energy at the explicit metallic Fermi radius is exactly `ε_F`. -/
theorem bandEnergy_upper_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0) (hmF : |m| ≤ fermiEnergy) :
    bandEnergy .upper v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy := by
  simpa using energy_metallicFermiRadius v m fermiEnergy hv hmF

/-- Positive radial energy is strictly increasing on the nonnegative axis when `v ≠ 0`. -/
theorem energy_radial_lt_of_lt_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hpq : p < q) :
    energy v m p 0 < energy v m q 0 := by
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hpSqLt : p ^ 2 < q ^ 2 := by
    nlinarith
  have henergySqLt : energy v m p 0 ^ 2 < energy v m q 0 ^ 2 := by
    rw [energy_sq, energy_sq]
    unfold energySq
    norm_num
    nlinarith
  have hpEnergy : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  have hqEnergy : 0 ≤ energy v m q 0 := Real.sqrt_nonneg _
  nlinarith

/-- In the metallic-or-band-edge regime `|m| ≤ ε_F`, the upper band is occupied exactly below the
explicit Fermi radius. At `ε_F = |m|`, this occupied region is empty and `p_F = 0`. -/
theorem bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
    (v m fermiEnergy p : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hp : 0 ≤ p) :
    bandEnergy .upper v m p 0 < fermiEnergy ↔
      p < metallicFermiRadius v m fermiEnergy := by
  rw [bandEnergy_upper]
  have hfermi := energy_metallicFermiRadius v m fermiEnergy hv hmF
  constructor
  · intro henergy
    by_contra hpF
    have hpFle : metallicFermiRadius v m fermiEnergy ≤ p := le_of_not_gt hpF
    rcases hpFle.eq_or_lt with hpEq | hpLt
    · have hfermi' := hfermi
      rw [hpEq] at hfermi'
      linarith
    · have hmono := energy_radial_lt_of_lt_of_nonneg
        v m (metallicFermiRadius v m fermiEnergy) p hv
        (metallicFermiRadius_nonneg v m fermiEnergy) hpLt
      linarith
  · intro hpLt
    have hmono := energy_radial_lt_of_lt_of_nonneg
      v m p (metallicFermiRadius v m fermiEnergy) hv hp hpLt
    rw [hfermi] at hmono
    exact hmono

/-- At positive Fermi energy, the lower band is occupied at every radial momentum. -/
theorem bandEnergy_lower_lt_fermi
    (v m fermiEnergy p : ℝ) (hfermi : 0 < fermiEnergy) :
    bandEnergy .lower v m p 0 < fermiEnergy := by
  rw [bandEnergy_lower]
  have henergy : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  linarith

/-- On the nonnegative radial axis in `|m| ≤ ε_F`, generic upper-band occupation is exactly
`p < p_F`; at the band edge `ε_F = |m|` this set is empty. -/
theorem mem_upperBand_radialOccupiedRegion_iff_lt_metallicFermiRadius
    (v m fermiEnergy p : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hp : 0 ≤ p) :
    p ∈ occupiedRegion (radialBandEnergy v m) fermiEnergy .upper ↔
      p < metallicFermiRadius v m fermiEnergy := by
  change bandEnergy .upper v m p 0 < fermiEnergy ↔
    p < metallicFermiRadius v m fermiEnergy
  exact bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
    v m fermiEnergy p hv hmF hp

/-- On the nonnegative radial axis in `|m| ≤ ε_F`, the generic upper-band Fermi surface is the
single explicit `metallicFermiRadius` value. -/
theorem mem_upperBand_radialFermiSurface_iff_eq_metallicFermiRadius
    (v m fermiEnergy p : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hp : 0 ≤ p) :
    p ∈ fermiSurface (radialBandEnergy v m) fermiEnergy .upper ↔
      p = metallicFermiRadius v m fermiEnergy := by
  constructor
  · intro hfermi
    change bandEnergy .upper v m p 0 = fermiEnergy at hfermi
    apply bandEnergy_radial_eq_imp_eq_of_nonneg
      .upper v m p (metallicFermiRadius v m fermiEnergy) hv hp
      (metallicFermiRadius_nonneg v m fermiEnergy)
    exact hfermi.trans
      (bandEnergy_upper_metallicFermiRadius v m fermiEnergy hv hmF).symm
  · intro hpF
    subst p
    change bandEnergy .upper v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy
    exact bandEnergy_upper_metallicFermiRadius v m fermiEnergy hv hmF

/-- Isotropic full-angle mean square of the `x` group-velocity component evaluated at the explicit
upper-band Fermi radius. -/
def isotropicFermiSurfaceMeanSquareVelocityX (v m fermiEnergy : ℝ) : ℝ :=
  isotropicMeanSquareRadialGroupVelocityX v m (metallicFermiRadius v m fermiEnergy)

/-- In the metallic-or-band-edge regime, the isotropic Fermi-surface factor is

`<v_x²>_FS = (v² / 2) * (1 - m² / ε_F²)`.
-/
theorem isotropicFermiSurfaceMeanSquareVelocityX_eq
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| ≤ fermiEnergy) (hfermi : fermiEnergy ≠ 0) :
    isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy =
      v ^ 2 * (1 - m ^ 2 / fermiEnergy ^ 2) / 2 := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq,
    radialEnergyDerivative_sq_metallicFermiRadius v m fermiEnergy hv hmF hfermi]

/-- In the strictly metallic regime `|m| < ε_F`, the isotropic Fermi-surface `v_x²` factor is
strictly positive when `v ≠ 0`. -/
theorem isotropicFermiSurfaceMeanSquareVelocityX_pos
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hmF : |m| < fermiEnergy) :
    0 < isotropicFermiSurfaceMeanSquareVelocityX v m fermiEnergy := by
  unfold isotropicFermiSurfaceMeanSquareVelocityX
  rw [isotropicMeanSquareRadialGroupVelocityX_eq]
  exact div_pos
    (radialEnergyDerivative_sq_metallicFermiRadius_pos v m fermiEnergy hv hmF)
    (by norm_num)

end

end QuantumTheory.Transport.Models.MassiveDirac
