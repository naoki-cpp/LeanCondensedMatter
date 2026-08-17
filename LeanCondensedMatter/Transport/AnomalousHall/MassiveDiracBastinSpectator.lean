import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinFermiSurface
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Spectator resolvent at a massive-Dirac Bastin pole

In an interband Bastin block, the retarded-minus-advanced spectral difference is singular at the
`target` band pole while the resolvent coefficient of the opposite `source` band remains regular.
This file isolates that regular factor before the occupation-weighted energy integration is closed.

At the target pole the opposite-band scalar resolvent is the inverse interband gap, and both its
retarded and advanced finite-broadening versions converge to that same value.  Their squares
therefore converge to the inverse squared gap.  No energy-limit interchange is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Away from the Dirac degeneracy, the two band energies are distinct. -/
theorem bandEnergy_ne_oppositeBandEnergy
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandEnergy band v m px py ≠ bandEnergy (oppositeBand band) v m px py := by
  have hgap : interbandEnergyGap band v m px py ≠ 0 := by
    rw [interbandEnergyGap_eq]
    cases band <;> simp [hE]
  exact sub_ne_zero.mp (by simpa [interbandEnergyGap] using hgap)

/-- Evaluating the opposite-band scalar resolvent at the selected band pole gives the inverse
interband energy gap exactly. -/
theorem projectorResolventCoefficient_oppositeBand_at_bandEnergy
    (band : Band) (v m px py : ℝ) :
    projectorResolventCoefficient
        ((bandEnergy band v m px py : ℝ) : ℂ)
        (oppositeBand band) v m px py =
      (((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹ := by
  simp [projectorResolventCoefficient, interbandEnergyGap]

/-- The retarded opposite-band coefficient is a regular spectator at the selected band pole and
converges to the inverse interband gap. -/
theorem tendsto_retarded_oppositeBandCoefficient_at_bandPole
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py)
      (nhds 0)
      (nhds ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹)) := by
  have h := tendsto_retarded_projectorResolventCoefficient_zero
    (oppositeBand band) v m px py (bandEnergy band v m px py)
    (bandEnergy_ne_oppositeBandEnergy band v m px py hE)
  simpa [projectorResolventCoefficient, interbandEnergyGap] using h

/-- The advanced opposite-band coefficient has the same regular pole value. -/
theorem tendsto_advanced_oppositeBandCoefficient_at_bandPole
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py)
      (nhds 0)
      (nhds ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹)) := by
  have h := tendsto_advanced_projectorResolventCoefficient_zero
    (oppositeBand band) v m px py (bandEnergy band v m px py)
    (bandEnergy_ne_oppositeBandEnergy band v m px py hE)
  simpa [projectorResolventCoefficient, interbandEnergyGap] using h

/-- Squaring the retarded spectator produces the inverse squared interband gap in the
zero-broadening limit. -/
theorem tendsto_retarded_oppositeBandCoefficient_sq_at_bandPole
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
  have h := tendsto_retarded_oppositeBandCoefficient_at_bandPole band v m px py hE
  simpa [pow_two] using h.mul h

/-- Squaring the advanced spectator gives the same inverse squared interband gap. -/
theorem tendsto_advanced_oppositeBandCoefficient_sq_at_bandPole
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
  have h := tendsto_advanced_oppositeBandCoefficient_at_bandPole band v m px py hE
  simpa [pow_two] using h.mul h

end

end AnomalousHall.MassiveDirac
