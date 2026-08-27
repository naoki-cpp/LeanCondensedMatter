import LeanCondensedMatter.Transport.Analysis.ZeroTemperatureOccupation
import Mathlib.Data.Set.Basic

set_option linter.style.header false

/-!
# Generic spectral occupation and band filling

This module records model-independent notions obtained from a band-energy function and an energy
occupation law.  Semiconductor-specific names such as `conduction` and `valence` do not appear
here: the primitive data are the spectrum and its occupation.

At zero temperature, the existing strict Fermi-step convention determines occupied momentum
regions and supports filled, empty, and partially filled band statements.  Finite-temperature
occupation laws can reuse `bandStateOccupation` without changing the band-energy layer.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {Band K : Type*}

/-- Occupation assigned to one band state by composing an energy occupation law with the spectrum. -/
def bandStateOccupation
    (occupation : ℝ → ℝ) (energy : Band → K → ℝ) (band : Band) (k : K) : ℝ :=
  occupation (energy band k)

/-- Zero-temperature occupied region of a band under the repository's strict Fermi-step convention. -/
def occupiedRegion
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) : Set K :=
  {k | energy band k < fermiEnergy}

/-- Fermi-surface locus of one band. -/
def fermiSurface
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) : Set K :=
  {k | energy band k = fermiEnergy}

/-- A band is filled at zero temperature when every state lies strictly below the Fermi energy. -/
def IsFilledBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) : Prop :=
  ∀ k, energy band k < fermiEnergy

/-- A band is empty at zero temperature when every state lies at or above the Fermi energy. -/
def IsEmptyBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) : Prop :=
  ∀ k, fermiEnergy ≤ energy band k

/-- A band is partially filled when it contains both occupied and unoccupied zero-temperature states. -/
def IsPartiallyFilledBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) : Prop :=
  (∃ k, energy band k < fermiEnergy) ∧
    (∃ k, fermiEnergy ≤ energy band k)

@[simp] theorem mem_occupiedRegion_iff
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K) :
    k ∈ occupiedRegion energy fermiEnergy band ↔ energy band k < fermiEnergy :=
  Iff.rfl

@[simp] theorem mem_fermiSurface_iff
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K) :
    k ∈ fermiSurface energy fermiEnergy band ↔ energy band k = fermiEnergy :=
  Iff.rfl

/-- Below the Fermi energy, the generic state occupation specialized to the zero-temperature step is
exactly one. -/
theorem bandStateOccupation_zeroTemperature_eq_one_of_lt
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K)
    (h : energy band k < fermiEnergy) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 1 := by
  simpa [bandStateOccupation] using
    zeroTemperatureOccupation_eq_one (fermiEnergy := fermiEnergy)
      (energy := energy band k) h

/-- At or above the Fermi energy, the generic state occupation specialized to the zero-temperature
step is exactly zero. -/
theorem bandStateOccupation_zeroTemperature_eq_zero_of_le
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K)
    (h : fermiEnergy ≤ energy band k) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 0 := by
  simpa [bandStateOccupation] using
    zeroTemperatureOccupation_eq_zero (fermiEnergy := fermiEnergy)
      (energy := energy band k) h

/-- Every state of a filled band has unit occupation under the strict zero-temperature Fermi step. -/
theorem bandStateOccupation_zeroTemperature_eq_one_of_isFilledBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band)
    (hfilled : IsFilledBand energy fermiEnergy band) (k : K) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 1 :=
  bandStateOccupation_zeroTemperature_eq_one_of_lt
    energy fermiEnergy band k (hfilled k)

/-- Every state of an empty band has zero occupation under the strict zero-temperature Fermi step. -/
theorem bandStateOccupation_zeroTemperature_eq_zero_of_isEmptyBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band)
    (hempty : IsEmptyBand energy fermiEnergy band) (k : K) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 0 :=
  bandStateOccupation_zeroTemperature_eq_zero_of_le
    energy fermiEnergy band k (hempty k)

/-- A zero-temperature state has occupation one exactly when it lies in the strict occupied region. -/
@[simp] theorem bandStateOccupation_zeroTemperature_eq_one_iff
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 1 ↔
      energy band k < fermiEnergy := by
  unfold bandStateOccupation zeroTemperatureOccupation
  by_cases h : energy band k < fermiEnergy <;> simp [h]

/-- A zero-temperature state has occupation zero exactly when it lies at or above the Fermi energy. -/
@[simp] theorem bandStateOccupation_zeroTemperature_eq_zero_iff
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band) (k : K) :
    bandStateOccupation (zeroTemperatureOccupation fermiEnergy) energy band k = 0 ↔
      fermiEnergy ≤ energy band k := by
  unfold bandStateOccupation zeroTemperatureOccupation
  by_cases h : energy band k < fermiEnergy
  · have hnot : ¬ fermiEnergy ≤ energy band k := not_le_of_gt h
    simp [h, hnot]
  · have hle : fermiEnergy ≤ energy band k := le_of_not_gt h
    simp [h, hle]

end
end Transport
end QuantumTheory
