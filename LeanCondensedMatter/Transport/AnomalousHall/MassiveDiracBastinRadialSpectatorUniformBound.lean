import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialResolventBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Explicit uniform bound for the radial massive-Dirac Bastin spectator

The radial spectator factorization and the mass-gap resolvent estimates combine into one explicit
bound independent of radial momentum, energy offset inside the target window, and broadening.
This is the model-specific domination input needed before integrating the Lorentzian pole.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Explicit uniform bound for the regular radial spectator/current factor. -/
def radialInterbandSpectatorUniformBound
    (e v m radius : ℝ) : ℝ :=
  2 * (radialBastinMassWindowMargin m radius)⁻¹ ^ 2 * (e ^ 2 * v ^ 2)

/-- The regular radial spectator/current factor is uniformly bounded throughout the fixed target
window, independently of momentum and broadening. -/
theorem norm_targetCenteredInterbandSpectatorCurrentFactor_radial_le
    (band : Band) (e v m p offset radius broadening : ℝ)
    (hm : 0 < m) (hradius : radius < 2 * m) (hoffset : |offset| ≤ radius) :
    ‖targetCenteredInterbandSpectatorCurrentFactor
        band e v m p 0 (offset, broadening)‖ ≤
      radialInterbandSpectatorUniformBound e v m radius := by
  have hE : energy v m p 0 ≠ 0 := ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
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
      band v m p offset radius broadening hm hradius hoffset
  have ha : ‖a‖ ≤ (radialBastinMassWindowMargin m radius)⁻¹ := by
    dsimp [a]
    exact norm_advancedRadialSpectatorResolvent_le_inv_margin
      band v m p offset radius broadening hm hradius hoffset
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
    exact norm_radialInterbandCurrentAmplitude_le band e v m p hm
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

end AnomalousHall.MassiveDirac
