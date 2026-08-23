import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialSpectatorBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Uniform radial resolvent bounds from the massive-Dirac mass gap

For a positive Dirac mass and a fixed target-centered energy window narrower than `2m`, the
opposite-band spectator pole stays a uniform positive distance away from the integration window.
The margin

```text
δ = 2m - radius
```

therefore bounds both retarded and advanced complex denominators from below, independently of
radial momentum and spectral broadening.  Their inverse norms are bounded by `δ⁻¹`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Momentum-independent separation between a target-centered window and the opposite-band pole. -/
def radialBastinMassWindowMargin (m radius : ℝ) : ℝ :=
  2 * m - radius

/-- A window narrower than the positive mass gap has strictly positive separation margin. -/
theorem radialBastinMassWindowMargin_pos
    (m radius : ℝ) (hradius : radius < 2 * m) :
    0 < radialBastinMassWindowMargin m radius := by
  exact sub_pos.mpr hradius

/-- The mass-window margin is a lower bound for the shifted real interband denominator at every
radial momentum. -/
theorem radialBastinMassWindowMargin_le_abs_gap_add_offset
    (band : Band) (v m p offset radius : ℝ) (hm : 0 < m)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      |interbandEnergyGap band v m p 0 + offset| := by
  have hgap : 2 * m ≤ |interbandEnergyGap band v m p 0| :=
    two_mul_mass_le_abs_interbandEnergyGap band v m p 0 hm.le
  have hshift :=
    abs_interbandEnergyGap_add_offset_ge_sub_radius
      band v m p 0 offset radius hoffset
  unfold radialBastinMassWindowMargin
  linarith

/-- The same real separation lower-bounds the norm of the retarded complex spectator denominator,
for arbitrary broadening. -/
theorem radialBastinMassWindowMargin_le_norm_retardedDenominator
    (band : Band) (v m p offset radius broadening : ℝ) (hm : 0 < m)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I‖ := by
  have hreal := radialBastinMassWindowMargin_le_abs_gap_add_offset
    band v m p offset radius hm hoffset
  have hre := Complex.abs_re_le_norm
    (((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
      (broadening : ℂ) * Complex.I)
  exact hreal.trans (by simpa using hre)

/-- The advanced complex spectator denominator has the same uniform norm lower bound. -/
theorem radialBastinMassWindowMargin_le_norm_advancedDenominator
    (band : Band) (v m p offset radius broadening : ℝ) (hm : 0 < m)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I‖ := by
  have hreal := radialBastinMassWindowMargin_le_abs_gap_add_offset
    band v m p offset radius hm hoffset
  have hre := Complex.abs_re_le_norm
    (((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
      (broadening : ℂ) * Complex.I)
  exact hreal.trans (by simpa using hre)

/-- The retarded opposite-band resolvent is uniformly bounded by the inverse mass-window margin. -/
theorem norm_retardedRadialSpectatorResolvent_le_inv_margin
    (band : Band) (v m p offset radius broadening : ℝ) (hm : 0 < m)
    (hradius : radius < 2 * m) (hoffset : |offset| ≤ radius) :
    ‖((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I)⁻¹)‖ ≤
      (radialBastinMassWindowMargin m radius)⁻¹ := by
  have hmargin : 0 < radialBastinMassWindowMargin m radius :=
    radialBastinMassWindowMargin_pos m radius hradius
  have hden := radialBastinMassWindowMargin_le_norm_retardedDenominator
    band v m p offset radius broadening hm hoffset
  have hnorm : 0 <
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I‖ :=
    lt_of_lt_of_le hmargin hden
  rw [norm_inv, inv_le_inv₀ hnorm hmargin]
  exact hden

/-- The advanced opposite-band resolvent obeys the same momentum- and broadening-independent
inverse-margin bound. -/
theorem norm_advancedRadialSpectatorResolvent_le_inv_margin
    (band : Band) (v m p offset radius broadening : ℝ) (hm : 0 < m)
    (hradius : radius < 2 * m) (hoffset : |offset| ≤ radius) :
    ‖((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I)⁻¹)‖ ≤
      (radialBastinMassWindowMargin m radius)⁻¹ := by
  have hmargin : 0 < radialBastinMassWindowMargin m radius :=
    radialBastinMassWindowMargin_pos m radius hradius
  have hden := radialBastinMassWindowMargin_le_norm_advancedDenominator
    band v m p offset radius broadening hm hoffset
  have hnorm : 0 <
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I‖ :=
    lt_of_lt_of_le hmargin hden
  rw [norm_inv, inv_le_inv₀ hnorm hmargin]
  exact hden

end

end AnomalousHall.MassiveDirac
