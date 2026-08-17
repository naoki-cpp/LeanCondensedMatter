import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Target-centered interband Bastin pole window

The occupation-weighted pole limit will integrate over a fixed energy window centered at a selected
massive-Dirac band energy.  The Lorentzian factor is singular at that target pole, but the
opposite-band spectator resolvent must remain uniformly separated from its own source-band pole.

This file rewrites the opposite-band retarded/advanced denominators in target-centered offset
coordinates and records the elementary real-gap separation needed for later uniform estimates.
No integral or limit/interchange theorem is proved here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Away from the Dirac degeneracy, the interband energy gap is nonzero. -/
theorem interbandEnergyGap_ne_zero_of_energy_ne_zero
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandEnergyGap band v m px py ≠ 0 := by
  unfold interbandEnergyGap
  exact sub_ne_zero.mpr (bandEnergy_ne_oppositeBandEnergy band v m px py hE)

/-- In target-centered offset coordinates, the retarded opposite-band spectator denominator is
`gap + offset + i η`. -/
theorem projectorResolventCoefficient_retarded_targetOffset_oppositeBand
    (band : Band) (v m px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (retardedSpectralParameter
          (bandEnergy band v m px py + offset) broadening)
        (oppositeBand band) v m px py =
      ((((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
          (broadening : ℂ) * Complex.I))⁻¹ := by
  unfold projectorResolventCoefficient retardedSpectralParameter interbandEnergyGap
  congr 1
  push_cast
  ring

/-- The advanced target-centered spectator denominator is `gap + offset - i η`. -/
theorem projectorResolventCoefficient_advanced_targetOffset_oppositeBand
    (band : Band) (v m px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (advancedSpectralParameter
          (bandEnergy band v m px py + offset) broadening)
        (oppositeBand band) v m px py =
      ((((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) -
          (broadening : ℂ) * Complex.I))⁻¹ := by
  unfold projectorResolventCoefficient advancedSpectralParameter interbandEnergyGap
  congr 1
  push_cast
  ring

/-- If `|offset| ≤ radius`, the shifted interband denominator stays at least
`|gap| - radius` away from zero on the real axis. -/
theorem abs_interbandEnergyGap_add_offset_ge_sub_radius
    (band : Band) (v m px py offset radius : ℝ)
    (hoffset : |offset| ≤ radius) :
    |interbandEnergyGap band v m px py| - radius ≤
      |interbandEnergyGap band v m px py + offset| := by
  have htri :
      |interbandEnergyGap band v m px py| ≤
        |interbandEnergyGap band v m px py + offset| + |offset| := by
    calc
      |interbandEnergyGap band v m px py| =
          |(interbandEnergyGap band v m px py + offset) + (-offset)| := by
            congr 1
            ring
      _ ≤ |interbandEnergyGap band v m px py + offset| + |-offset| :=
        abs_add _ _
      _ = |interbandEnergyGap band v m px py + offset| + |offset| := by
        rw [abs_neg]
  linarith

/-- A target-centered window narrower than the interband gap cannot contain the opposite-band
source pole. -/
theorem interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    interbandEnergyGap band v m px py + offset ≠ 0 := by
  have hgap := interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hgapAbs : 0 < |interbandEnergyGap band v m px py| := abs_pos.mpr hgap
  have hlower := abs_interbandEnergyGap_add_offset_ge_sub_radius
    band v m px py offset radius hoffset
  have hshiftAbs : 0 < |interbandEnergyGap band v m px py + offset| := by
    have : 0 < |interbandEnergyGap band v m px py| - radius := sub_pos.mpr hradius
    exact lt_of_lt_of_le this hlower
  exact abs_pos.mp hshiftAbs

/-- The retarded complex spectator denominator is nonzero throughout such a target-centered window,
for every real broadening. -/
theorem retardedSpectatorDenominator_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius broadening : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    ((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I ≠ 0 := by
  have hreal := interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    band v m px py offset radius hE hradius hoffset
  intro hzero
  apply hreal
  simpa using congrArg Complex.re hzero

/-- The advanced complex spectator denominator is likewise nonzero on the same window. -/
theorem advancedSpectatorDenominator_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius broadening : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    ((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I ≠ 0 := by
  have hreal := interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    band v m px py offset radius hE hradius hoffset
  intro hzero
  apply hreal
  simpa using congrArg Complex.re hzero

end

end AnomalousHall.MassiveDirac
