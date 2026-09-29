import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Limit
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Spectator resolvent at a Rashba-exchange Bastin pole

At a target-band pole, the opposite-band scalar resolvent remains regular.  Its zero-broadening
limit is the inverse interband gap, providing the regular spectator factor used by the fixed-window
clean-limit extraction.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

theorem projectorResolventCoefficient_oppositeBand_at_bandEnergy
    (params : Parameters) (band : Band) (px py : ℝ) :
    projectorResolventCoefficient
        ((bandEnergy params band px py : ℝ) : ℂ)
        params (oppositeBand band) px py =
      (((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹ := by
  simp [projectorResolventCoefficient, interbandEnergyGap]

theorem tendsto_oppositeBandCoefficient_at_bandPole
    (side : SpectralSide) (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy params band px py) broadening)
          params (oppositeBand band) px py)
      (nhds 0)
      (nhds ((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹)) := by
  have h := tendsto_projectorResolventCoefficient_zero
    side params (oppositeBand band) px py (bandEnergy params band px py)
    (bandEnergy_ne_oppositeBandEnergy params band px py hE)
  simpa [projectorResolventCoefficient, interbandEnergyGap] using h

theorem tendsto_oppositeBandCoefficient_sq_at_bandPole
    (side : SpectralSide) (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy params band px py) broadening)
          params (oppositeBand band) px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
  have h := tendsto_oppositeBandCoefficient_at_bandPole
    side params band px py hE
  simpa [pow_two] using h.mul h

end

end QuantumTheory.Transport.Models.RashbaExchange
