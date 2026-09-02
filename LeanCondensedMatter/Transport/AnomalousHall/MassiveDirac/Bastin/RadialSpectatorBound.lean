import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialDomination
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial spectator factorization for massive-Dirac Bastin domination

On the radial momentum axis the two interband current blocks are purely imaginary with opposite
signs.  Consequently the regular spectator/current factor is the sum of the squared retarded and
advanced opposite-band resolvents multiplying one common current amplitude.

This factorization separates the two estimates required by the finite-radial dominated-convergence
step: the current amplitude is controlled by `m / E ≤ 1`, while the resolvent denominators are
controlled by the positive mass gap and a fixed target window `radius < 2m`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Common purely-imaginary current amplitude in the radial interband Bastin blocks. -/
def radialInterbandCurrentAmplitude
    (band : Band) (e v m p : ℝ) : ℂ :=
  (((e ^ 2 : ℝ) : ℂ)) *
    (((bandSign band * m * v ^ 2 / energy v m p 0 : ℝ) : ℂ)) * Complex.I

/-- The radial spectator/current factor is exactly the sum of the retarded and advanced squared
opposite-band resolvents times the common radial current amplitude. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_radial_eq
    (band : Band) (e v m p offset broadening : ℝ)
    (hE : energy v m p 0 ≠ 0) :
    targetCenteredInterbandSpectatorCurrentFactor
        band e v m p 0 (offset, broadening) =
      (((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
          (broadening : ℂ) * Complex.I)⁻¹) ^ 2 +
        ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
          (broadening : ℂ) * Complex.I)⁻¹) ^ 2) *
        radialInterbandCurrentAmplitude band e v m p := by
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
    radialInterbandCurrentAmplitude
  dsimp
  rw [projectorResolventCoefficient_retarded_targetOffset_oppositeBand,
    projectorResolventCoefficient_advanced_targetOffset_oppositeBand,
    bastinXYBandBlockTrace_opposite_source_radial band e v m p hE,
    bastinYXBandBlockTrace_opposite_source_radial band e v m p hE]
  ring

/-- The real coefficient of the radial current amplitude is bounded by `v²`; the mass-to-energy
ratio cannot exceed one for positive mass. -/
theorem abs_radialInterbandCurrentCoefficient_le_velocity_sq
    (band : Band) (v m p : ℝ) (hm : 0 < m) :
    |bandSign band * m * v ^ 2 / energy v m p 0| ≤ v ^ 2 := by
  have hE : 0 < energy v m p 0 := energy_pos_of_mass_pos v m p 0 hm
  have hmE : m ≤ energy v m p 0 := mass_le_energy v m p 0
  have hratio : 0 ≤ m * v ^ 2 / energy v m p 0 :=
    div_nonneg (mul_nonneg hm.le (sq_nonneg v)) hE.le
  have hratio_le : m * v ^ 2 / energy v m p 0 ≤ v ^ 2 := by
    rw [div_le_iff₀ hE]
    calc
      m * v ^ 2 ≤ energy v m p 0 * v ^ 2 :=
        mul_le_mul_of_nonneg_right hmE (sq_nonneg v)
      _ = v ^ 2 * energy v m p 0 := by ring
  cases band with
  | lower =>
      rw [show bandSign .lower * m * v ^ 2 / energy v m p 0 =
        -(m * v ^ 2 / energy v m p 0) by simp [bandSign]; ring]
      rw [abs_neg, abs_of_nonneg hratio]
      exact hratio_le
  | upper =>
      simpa [bandSign, abs_of_nonneg hratio] using hratio_le

/-- The norm of the common radial interband current amplitude is uniformly bounded in momentum by
`e² v²`. -/
theorem norm_radialInterbandCurrentAmplitude_le
    (band : Band) (e v m p : ℝ) (hm : 0 < m) :
    ‖radialInterbandCurrentAmplitude band e v m p‖ ≤ e ^ 2 * v ^ 2 := by
  have hcoeff :=
    abs_radialInterbandCurrentCoefficient_le_velocity_sq band v m p hm
  unfold radialInterbandCurrentAmplitude
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg e)]
  exact mul_le_mul_of_nonneg_left hcoeff (sq_nonneg e)

end

end AnomalousHall.MassiveDirac
