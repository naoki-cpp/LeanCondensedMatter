import LeanCondensedMatter.Models.MassiveDirac.Model.FermiSurface
import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureBandFilling

set_option linter.style.header false

/-!
# Spectral occupation of the massive-Dirac bands

This module specializes the generic zero-temperature occupation and band-filling predicates to
the two-dimensional massive-Dirac dispersion. The Fermi radius and radial energy identities are
owned by `Model.FermiSurface`, independently of occupation or temperature.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Massive-Dirac band energy regarded as a function on two-dimensional physical momentum. -/
def bandEnergyOnMomentum (v m : ℝ) (band : Band) (p : ℝ × ℝ) : ℝ :=
  bandEnergy band v m p.1 p.2

/-- Any massive-Dirac lower band is filled when the Fermi energy is positive. -/
theorem lowerBand_isFilled_of_pos_fermiEnergy
    (v m fermiEnergy : ℝ) (hfermi : 0 < fermiEnergy) :
    IsFilledBand (bandEnergyOnMomentum v m) fermiEnergy .lower := by
  intro p
  simp only [bandEnergyOnMomentum, bandEnergy_lower]
  have henergy : 0 ≤ energy v m p.1 p.2 := Real.sqrt_nonneg _
  linarith

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
    rw [bandEnergy_upper] at hfermi
    apply energy_radial_eq_imp_eq_of_nonneg
      v m p (metallicFermiRadius v m fermiEnergy) hv hp
      (metallicFermiRadius_nonneg v m fermiEnergy)
    exact hfermi.trans
      (energy_metallicFermiRadius v m fermiEnergy hv hmF).symm
  · intro hpF
    subst p
    change bandEnergy .upper v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy
    simpa using energy_metallicFermiRadius v m fermiEnergy hv hmF

end

end QuantumTheory.Models.MassiveDirac
