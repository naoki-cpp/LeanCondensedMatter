import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Target-centered interband Bastin pole window

The occupation-weighted pole limit will integrate over a fixed energy window centered at a selected
massive-Dirac band energy.  The Lorentzian factor is singular at that target pole, but the
opposite-band spectator resolvent must remain uniformly separated from its own source-band pole.

This file rewrites the opposite-band spectral-side denominator in target-centered offset coordinates
and records the elementary real-gap separation needed for later uniform estimates. Conventional
retarded/advanced theorem names remain as specializations. No integral or limit/interchange theorem
is proved here.
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

/-- In target-centered offset coordinates, the opposite-band spectator denominator on spectral side
`s` is `gap + offset + s i η`. -/
theorem projectorResolventCoefficient_targetOffset_oppositeBand
    (side : SpectralSide) (band : Band) (v m px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (spectralParameter side
          (bandEnergy band v m px py + offset) broadening)
        (oppositeBand band) v m px py =
      ((((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
          ((side.sign * broadening : ℝ) : ℂ) * Complex.I))⁻¹ := by
  unfold projectorResolventCoefficient spectralParameter spectralParameterOfRegulator
    interbandEnergyGap
  congr 1
  push_cast
  ring

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
  simpa only [spectralParameter_retarded, SpectralSide.sign_retarded, one_mul] using
    projectorResolventCoefficient_targetOffset_oppositeBand
      .retarded band v m px py offset broadening

/-- The advanced target-centered spectator denominator is `gap + offset - i η`. -/
theorem projectorResolventCoefficient_advanced_targetOffset_oppositeBand
    (band : Band) (v m px py offset broadening : ℝ) :
    projectorResolventCoefficient
        (advancedSpectralParameter
          (bandEnergy band v m px py + offset) broadening)
        (oppositeBand band) v m px py =
      ((((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) -
          (broadening : ℂ) * Complex.I))⁻¹ := by
  simpa [spectralParameter_advanced, SpectralSide.sign_advanced, sub_eq_add_neg] using
    projectorResolventCoefficient_targetOffset_oppositeBand
      .advanced band v m px py offset broadening

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
        abs_add_le _ _
      _ = |interbandEnergyGap band v m px py + offset| + |offset| := by
        rw [abs_neg]
  linarith

/-- A target-centered window narrower than the interband gap cannot contain the opposite-band
source pole. -/
theorem interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    interbandEnergyGap band v m px py + offset ≠ 0 := by
  have hlower := abs_interbandEnergyGap_add_offset_ge_sub_radius
    band v m px py offset radius hoffset
  have hshiftAbs : 0 < |interbandEnergyGap band v m px py + offset| := by
    have hpositive : 0 < |interbandEnergyGap band v m px py| - radius :=
      sub_pos.mpr hradius
    exact lt_of_lt_of_le hpositive hlower
  exact abs_pos.mp hshiftAbs

/-- On either spectral side, the complex spectator denominator is nonzero throughout a
sufficiently narrow target-centered window, for every real broadening. -/
theorem spectralSideSpectatorDenominator_ne_zero_on_targetWindow
    (side : SpectralSide) (band : Band) (v m px py offset radius broadening : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    ((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
        ((side.sign * broadening : ℝ) : ℂ) * Complex.I ≠ 0 := by
  have hreal := interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    band v m px py offset radius hradius hoffset
  intro hzero
  apply hreal
  simpa using congrArg Complex.re hzero

/-- The retarded complex spectator denominator is nonzero throughout such a target-centered window,
for every real broadening. -/
theorem retardedSpectatorDenominator_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius broadening : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    ((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I ≠ 0 := by
  simpa only [SpectralSide.sign_retarded, one_mul] using
    spectralSideSpectatorDenominator_ne_zero_on_targetWindow
      .retarded band v m px py offset radius broadening hradius hoffset

/-- The advanced complex spectator denominator is likewise nonzero on the same window. -/
theorem advancedSpectatorDenominator_ne_zero_on_targetWindow
    (band : Band) (v m px py offset radius broadening : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |offset| ≤ radius) :
    ((interbandEnergyGap band v m px py + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I ≠ 0 := by
  simpa [SpectralSide.sign_advanced, sub_eq_add_neg] using
    spectralSideSpectatorDenominator_ne_zero_on_targetWindow
      .advanced band v m px py offset radius broadening hradius hoffset

end

end AnomalousHall.MassiveDirac
