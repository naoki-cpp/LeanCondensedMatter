import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialSpectatorBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Uniform radial spectator bounds from the massive-Dirac mass gap

The radial spectator factorization and the mass-magnitude gap give a momentum-independent separation
between a fixed target-centered energy window and the opposite-band pole. This file packages that
mass-window margin, the resulting retarded/advanced resolvent bounds, and the explicit uniform bound
for the complete regular spectator/current factor.

The resulting bound is independent of radial momentum, energy offset inside the target window, and
broadening. It is the model-specific domination input used before integrating the Lorentzian pole.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Momentum-independent separation between a target-centered window and the opposite-band pole. -/
def radialBastinMassWindowMargin (m radius : ℝ) : ℝ :=
  2 * |m| - radius

/-- A window narrower than the mass-magnitude gap has strictly positive separation margin. -/
theorem radialBastinMassWindowMargin_pos
    (m radius : ℝ) (hradius : radius < 2 * |m|) :
    0 < radialBastinMassWindowMargin m radius := by
  exact sub_pos.mpr hradius

/-- The mass-window margin is a lower bound for the shifted real interband denominator at every
radial momentum. -/
theorem radialBastinMassWindowMargin_le_abs_gap_add_offset
    (band : Band) (v m p offset radius : ℝ)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      |interbandEnergyGap band v m p 0 + offset| := by
  have hgap : 2 * |m| ≤ |interbandEnergyGap band v m p 0| :=
    two_mul_abs_mass_le_abs_interbandEnergyGap band v m p 0
  have hshift :=
    abs_interbandEnergyGap_add_offset_ge_sub_radius
      band v m p 0 offset radius hoffset
  unfold radialBastinMassWindowMargin
  linarith

/-- The same real separation lower-bounds the norm of the retarded complex spectator denominator,
for arbitrary broadening. -/
theorem radialBastinMassWindowMargin_le_norm_retardedDenominator
    (band : Band) (v m p offset radius broadening : ℝ)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I‖ := by
  have hreal := radialBastinMassWindowMargin_le_abs_gap_add_offset
    band v m p offset radius hoffset
  have hre := Complex.abs_re_le_norm
    (((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
      (broadening : ℂ) * Complex.I)
  exact hreal.trans (by simpa using hre)

/-- The advanced complex spectator denominator has the same uniform norm lower bound. -/
theorem radialBastinMassWindowMargin_le_norm_advancedDenominator
    (band : Band) (v m p offset radius broadening : ℝ)
    (hoffset : |offset| ≤ radius) :
    radialBastinMassWindowMargin m radius ≤
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I‖ := by
  have hreal := radialBastinMassWindowMargin_le_abs_gap_add_offset
    band v m p offset radius hoffset
  have hre := Complex.abs_re_le_norm
    (((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
      (broadening : ℂ) * Complex.I)
  exact hreal.trans (by simpa using hre)

/-- The retarded opposite-band resolvent is uniformly bounded by the inverse mass-window margin. -/
theorem norm_retardedRadialSpectatorResolvent_le_inv_margin
    (band : Band) (v m p offset radius broadening : ℝ)
    (hradius : radius < 2 * |m|) (hoffset : |offset| ≤ radius) :
    ‖((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I)⁻¹)‖ ≤
      (radialBastinMassWindowMargin m radius)⁻¹ := by
  have hmargin : 0 < radialBastinMassWindowMargin m radius :=
    radialBastinMassWindowMargin_pos m radius hradius
  have hden := radialBastinMassWindowMargin_le_norm_retardedDenominator
    band v m p offset radius broadening hoffset
  have hnorm : 0 <
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
        (broadening : ℂ) * Complex.I‖ :=
    lt_of_lt_of_le hmargin hden
  rw [norm_inv, inv_le_inv₀ hnorm hmargin]
  exact hden

/-- The advanced opposite-band resolvent obeys the same momentum- and broadening-independent
inverse-margin bound. -/
theorem norm_advancedRadialSpectatorResolvent_le_inv_margin
    (band : Band) (v m p offset radius broadening : ℝ)
    (hradius : radius < 2 * |m|) (hoffset : |offset| ≤ radius) :
    ‖((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I)⁻¹)‖ ≤
      (radialBastinMassWindowMargin m radius)⁻¹ := by
  have hmargin : 0 < radialBastinMassWindowMargin m radius :=
    radialBastinMassWindowMargin_pos m radius hradius
  have hden := radialBastinMassWindowMargin_le_norm_advancedDenominator
    band v m p offset radius broadening hoffset
  have hnorm : 0 <
      ‖((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
        (broadening : ℂ) * Complex.I‖ :=
    lt_of_lt_of_le hmargin hden
  rw [norm_inv, inv_le_inv₀ hnorm hmargin]
  exact hden

/-- Explicit uniform bound for the regular radial spectator/current factor. -/
def radialInterbandSpectatorUniformBound
    (e v m radius : ℝ) : ℝ :=
  2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 * (e ^ 2 * v ^ 2)

/-- The regular radial spectator/current factor is uniformly bounded throughout the fixed target
window, independently of momentum and broadening. -/
theorem norm_targetCenteredInterbandSpectatorCurrentFactor_radial_le
    (band : Band) (e v m p offset radius broadening : ℝ)
    (hm : m ≠ 0) (hradius : radius < 2 * |m|) (hoffset : |offset| ≤ radius) :
    ‖targetCenteredInterbandSpectatorCurrentFactor
        band e v m p 0 (offset, broadening)‖ ≤
      radialInterbandSpectatorUniformBound e v m radius := by
  have hE : energy v m p 0 ≠ 0 := ne_of_gt (energy_pos_of_mass_ne_zero v m p 0 hm)
  rw [targetCenteredInterbandSpectatorCurrentFactor_radial_eq
    band e v m p offset broadening hE]
  let r : ℂ :=
    ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
      (broadening : ℂ) * Complex.I)⁻¹)
  let a : ℂ :=
    ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
      (broadening : ℂ) * Complex.I)⁻¹)
  let A : ℂ := radialInterbandCurrentAmplitude band e v m p
  have hr : ‖r‖ ≤ (radialBastinMassWindowMargin m radius)⁻¹ := by
    dsimp [r]
    exact norm_retardedRadialSpectatorResolvent_le_inv_margin
      band v m p offset radius broadening hradius hoffset
  have ha : ‖a‖ ≤ (radialBastinMassWindowMargin m radius)⁻¹ := by
    dsimp [a]
    exact norm_advancedRadialSpectatorResolvent_le_inv_margin
      band v m p offset radius broadening hradius hoffset
  have hr2 : ‖r ^ 2‖ ≤ (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg r) hr 2
  have ha2 : ‖a ^ 2‖ ≤ (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hsum :
      ‖r ^ 2 + a ^ 2‖ ≤ 2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := by
    calc
      ‖r ^ 2 + a ^ 2‖ ≤ ‖r ^ 2‖ + ‖a ^ 2‖ := norm_add_le _ _
      _ ≤ (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 +
          (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := add_le_add hr2 ha2
      _ = 2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := by ring
  have hA : ‖A‖ ≤ e ^ 2 * v ^ 2 := by
    dsimp [A]
    exact norm_radialInterbandCurrentAmplitude_le band e v m p
  have hupper : 0 ≤ 2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 := by
    positivity
  change ‖(r ^ 2 + a ^ 2) * A‖ ≤ radialInterbandSpectatorUniformBound e v m radius
  rw [norm_mul]
  calc
    ‖r ^ 2 + a ^ 2‖ * ‖A‖ ≤
        (2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2) * (e ^ 2 * v ^ 2) :=
      mul_le_mul hsum hA (norm_nonneg A) hupper
    _ = radialInterbandSpectatorUniformBound e v m radius := by
      rfl

end

end QuantumTheory.Transport.Models.MassiveDirac
