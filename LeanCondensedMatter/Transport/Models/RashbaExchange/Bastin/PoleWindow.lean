import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Target-centered Rashba-exchange interband pole window

The target-band Lorentzian pole is integrated over a fixed energy window while the opposite-band
spectator must remain separated from its own pole.  This module records the exact shifted-gap
denominator and the elementary real-gap separation.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport

theorem projectorResolventCoefficient_targetOffset_oppositeBand
    (side : SpectralSide) (params : Parameters) (band : Band)
    (px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (spectralParameter side
          (bandEnergy params band px py + offset) broadening)
        params (oppositeBand band) px py =
      ((((interbandEnergyGap params band px py + offset : ℝ) : ℂ) +
          ((side.regulator broadening : ℝ) : ℂ) * Complex.I))⁻¹ := by
  unfold projectorResolventCoefficient spectralParameter spectralParameterOfRegulator
    interbandEnergyGap
  congr 1
  push_cast
  ring

theorem abs_interbandEnergyGap_add_offset_ge_sub_radius
    (params : Parameters) (band : Band) (px py offset radius : ℝ)
    (hoffset : |offset| ≤ radius) :
    |interbandEnergyGap params band px py| - radius ≤
      |interbandEnergyGap params band px py + offset| := by
  have htri :
      |interbandEnergyGap params band px py| ≤
        |interbandEnergyGap params band px py + offset| + |offset| := by
    calc
      |interbandEnergyGap params band px py| =
          |(interbandEnergyGap params band px py + offset) + (-offset)| := by
            congr 1
            ring
      _ ≤ |interbandEnergyGap params band px py + offset| + |-offset| :=
        abs_add_le _ _
      _ = |interbandEnergyGap params band px py + offset| + |offset| := by
        rw [abs_neg]
  linarith

theorem interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    (params : Parameters) (band : Band) (px py offset radius : ℝ)
    (hradius : radius < |interbandEnergyGap params band px py|)
    (hoffset : |offset| ≤ radius) :
    interbandEnergyGap params band px py + offset ≠ 0 := by
  have hlower := abs_interbandEnergyGap_add_offset_ge_sub_radius
    params band px py offset radius hoffset
  have hshiftAbs : 0 < |interbandEnergyGap params band px py + offset| := by
    have hpositive : 0 < |interbandEnergyGap params band px py| - radius :=
      sub_pos.mpr hradius
    exact lt_of_lt_of_le hpositive hlower
  exact abs_pos.mp hshiftAbs

end

end QuantumTheory.Transport.Models.RashbaExchange
