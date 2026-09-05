import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Limit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Spectator resolvent at a massive-Dirac Bastin pole

In an interband Bastin block, the retarded-minus-advanced spectral difference is singular at the
`target` band pole while the resolvent coefficient of the opposite `source` band remains regular.
This file isolates that regular factor before the occupation-weighted energy integration is closed.

At the target pole the opposite-band scalar resolvent is the inverse interband gap.  The canonical
side-indexed finite-broadening coefficient converges to that value on either spectral side, and its
square therefore converges to the inverse squared gap. No energy-limit interchange is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Evaluating the opposite-band scalar resolvent at the selected band pole gives the inverse
interband energy gap exactly. -/
theorem projectorResolventCoefficient_oppositeBand_at_bandEnergy
    (band : Band) (v m px py : ℝ) :
    projectorResolventCoefficient
        ((bandEnergy band v m px py : ℝ) : ℂ)
        (oppositeBand band) v m px py =
      (((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹ := by
  simp [projectorResolventCoefficient, interbandEnergyGap]

/-- On either spectral side, the opposite-band coefficient is a regular spectator at the selected
band pole and converges to the inverse interband gap. -/
theorem tendsto_oppositeBandCoefficient_at_bandPole
    (side : SpectralSide) (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py)
      (nhds 0)
      (nhds ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹)) := by
  have h := tendsto_projectorResolventCoefficient_zero
    side (oppositeBand band) v m px py (bandEnergy band v m px py)
    (bandEnergy_ne_oppositeBandEnergy band v m px py hE)
  simpa [projectorResolventCoefficient, interbandEnergyGap] using h

/-- Squaring the spectator on either spectral side produces the inverse squared interband gap in the
zero-broadening limit. -/
theorem tendsto_oppositeBandCoefficient_sq_at_bandPole
    (side : SpectralSide) (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy band v m px py) broadening)
          (oppositeBand band) v m px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
  have h := tendsto_oppositeBandCoefficient_at_bandPole side band v m px py hE
  simpa [pow_two] using h.mul h

end

end AnomalousHall.MassiveDirac
