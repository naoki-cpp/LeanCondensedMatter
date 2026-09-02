import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.RadialDomination
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial spectator factorization for massive-Dirac Bastin domination

On the radial momentum axis the two interband current blocks are purely imaginary with opposite
signs.  Consequently the regular spectator/current factor is the sum of the squared retarded and
advanced opposite-band resolvents multiplying one common current amplitude.

This factorization separates the two estimates required by the finite-radial dominated-convergence
step: the current amplitude is controlled by `|m| / E ≤ 1`, while the resolvent denominators are
controlled by the mass-magnitude gap and a fixed target window `radius < 2|m|`.
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
  have hret :
      projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m p 0 + offset) broadening)
          (oppositeBand band) v m p 0 =
        ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
            (broadening : ℂ) * Complex.I))⁻¹ := by
    simpa only [spectralParameter_retarded, SpectralSide.sign_retarded, one_mul] using
      projectorResolventCoefficient_targetOffset_oppositeBand
        .retarded band v m p 0 offset broadening
  have hadv :
      projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m p 0 + offset) broadening)
          (oppositeBand band) v m p 0 =
        ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
            (broadening : ℂ) * Complex.I))⁻¹ := by
    simpa [spectralParameter_advanced, SpectralSide.sign_advanced, sub_eq_add_neg] using
      projectorResolventCoefficient_targetOffset_oppositeBand
        .advanced band v m p 0 offset broadening
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
    radialInterbandCurrentAmplitude
  dsimp
  rw [hret, hadv,
    bastinXYBandBlockTrace_opposite_source_radial band e v m p hE,
    bastinYXBandBlockTrace_opposite_source_radial band e v m p hE]
  ring

/-- The real coefficient of the radial current amplitude is bounded by `v²`; the mass-magnitude to
energy ratio cannot exceed one. -/
theorem abs_radialInterbandCurrentCoefficient_le_velocity_sq
    (band : Band) (v m p : ℝ) :
    |bandSign band * m * v ^ 2 / energy v m p 0| ≤ v ^ 2 := by
  by_cases hm : m = 0
  · subst m
    simpa using (sq_nonneg v)
  · have hE : 0 < energy v m p 0 := energy_pos_of_mass_ne_zero v m p 0 hm
    have hmE : |m| ≤ energy v m p 0 := abs_mass_le_energy v m p 0
    have hratio : |m| * v ^ 2 / energy v m p 0 ≤ v ^ 2 := by
      rw [div_le_iff₀ hE]
      calc
        |m| * v ^ 2 ≤ energy v m p 0 * v ^ 2 :=
          mul_le_mul_of_nonneg_right hmE (sq_nonneg v)
        _ = v ^ 2 * energy v m p 0 := by ring
    cases band <;>
      simpa [bandSign, abs_div, abs_mul, abs_of_nonneg (sq_nonneg v), abs_of_pos hE] using hratio

/-- The norm of the common radial interband current amplitude is uniformly bounded in momentum by
`e² v²`. -/
theorem norm_radialInterbandCurrentAmplitude_le
    (band : Band) (e v m p : ℝ) :
    ‖radialInterbandCurrentAmplitude band e v m p‖ ≤ e ^ 2 * v ^ 2 := by
  have hcoeff :=
    abs_radialInterbandCurrentCoefficient_le_velocity_sq band v m p
  unfold radialInterbandCurrentAmplitude
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg e)]
  exact mul_le_mul_of_nonneg_left hcoeff (sq_nonneg e)

end

end AnomalousHall.MassiveDirac
