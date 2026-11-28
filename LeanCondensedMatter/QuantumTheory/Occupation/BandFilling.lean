import LeanCondensedMatter.QuantumTheory.Occupation.ZeroTemperature
import Mathlib.Data.Set.Basic

set_option linter.style.header false

/-!
# Spectral zero-temperature band filling

This module owns model-independent zero-temperature occupied regions, Fermi surfaces, and filled,
empty, and partially filled band predicates under the repository's strict `energy < fermiEnergy`
convention. It also connects those predicates to the scalar zero-temperature occupation law.

These definitions belong to the spectral occupation layer; transport-specific Lorentzian Fermi-edge
integrals and broadening limits remain downstream in `Transport.Analysis.ZeroTemperatureLorentzian`.
-/

namespace QuantumTheory

noncomputable section

variable {Band K : Type*}

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

/-- Every state of a filled band has unit occupation under the strict zero-temperature Fermi step. -/
theorem zeroTemperatureOccupation_eq_one_of_isFilledBand
    (energy : Band → K → ℝ) (fermiEnergy : ℝ) (band : Band)
    (hfilled : IsFilledBand energy fermiEnergy band) (k : K) :
    zeroTemperatureOccupation fermiEnergy (energy band k) = 1 :=
  zeroTemperatureOccupation_eq_one (hfilled k)

end
end QuantumTheory
