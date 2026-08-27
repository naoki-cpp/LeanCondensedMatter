import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import LeanCondensedMatter.Transport.Analysis.BandOccupation

set_option linter.style.header false

/-!
# Spectral occupation of the massive-Dirac bands

This file connects the concrete two-band massive-Dirac spectrum to the generic transport
band-occupation layer.  The spectral labels remain `lower` and `upper`; semiconductor-specific
`valence` / `conduction` terminology is downstream interpretation rather than primitive data.
-/

namespace AnomalousHall.MassiveDirac

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

/-- The upper-band zero-temperature occupied region is exactly the region where the positive Dirac
energy lies below the Fermi energy. -/
@[simp] theorem mem_upperBand_occupiedRegion_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    p ∈ occupiedRegion (bandEnergyOnMomentum v m) fermiEnergy .upper ↔
      energy v m p.1 p.2 < fermiEnergy := by
  simp [occupiedRegion, bandEnergyOnMomentum]

/-- The upper-band Fermi surface is the level set of the positive Dirac energy. -/
@[simp] theorem mem_upperBand_fermiSurface_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    p ∈ fermiSurface (bandEnergyOnMomentum v m) fermiEnergy .upper ↔
      energy v m p.1 p.2 = fermiEnergy := by
  simp [fermiSurface, bandEnergyOnMomentum]

/-- Every lower-band state has unit zero-temperature occupation at positive Fermi energy. -/
theorem lowerBand_zeroTemperatureOccupation_eq_one
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) (hfermi : 0 < fermiEnergy) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
        (bandEnergyOnMomentum v m) .lower p = 1 := by
  apply bandStateOccupation_zeroTemperature_eq_one_of_lt
  exact lowerBand_isFilled_of_pos_fermiEnergy v m fermiEnergy hfermi p

/-- Upper-band zero-temperature occupation is one exactly below the positive-energy Fermi surface. -/
@[simp] theorem upperBand_zeroTemperatureOccupation_eq_one_iff
    (v m fermiEnergy : ℝ) (p : ℝ × ℝ) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy)
        (bandEnergyOnMomentum v m) .upper p = 1 ↔
      energy v m p.1 p.2 < fermiEnergy := by
  rw [bandStateOccupation_zeroTemperature_eq_one_iff]
  simp [bandEnergyOnMomentum]

end

end AnomalousHall.MassiveDirac
