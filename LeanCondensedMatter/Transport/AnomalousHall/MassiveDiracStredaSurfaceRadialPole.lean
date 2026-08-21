import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfacePoleContinuity
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialSpectatorBound
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial form of the massive-Dirac Středa surface pole

On the radial momentum axis the two interband current orderings are purely imaginary with opposite
signs.  The regular Středa surface spectator therefore reduces to the sum of the retarded and
advanced opposite-band scalar resolvents multiplying the common radial current amplitude.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Exact radial target-centered Středa surface spectator. -/
theorem targetCenteredStredaSurfaceSpectatorCurrentFactor_radial_eq
    (band : Band) (e v m p offset broadening : ℝ)
    (hE : energy v m p 0 ≠ 0) :
    targetCenteredStredaSurfaceSpectatorCurrentFactor
        band e v m p 0 (offset, broadening) =
      (((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
          (broadening : ℂ) * Complex.I)⁻¹) +
        ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
          (broadening : ℂ) * Complex.I)⁻¹)) *
        radialInterbandCurrentAmplitude band e v m p := by
  unfold targetCenteredStredaSurfaceSpectatorCurrentFactor
    stredaSurfaceSpectatorCurrentFactor
  dsimp
  rw [projectorResolventCoefficient_retarded_targetOffset_oppositeBand,
    projectorResolventCoefficient_advanced_targetOffset_oppositeBand,
    bastinXYBandBlockTrace_opposite_source_radial band e v m p hE,
    bastinYXBandBlockTrace_opposite_source_radial band e v m p hE]
  change
    (((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) +
          (broadening : ℂ) * Complex.I)⁻¹) *
        radialInterbandCurrentAmplitude band e v m p -
      ((((interbandEnergyGap band v m p 0 + offset : ℝ) : ℂ) -
          (broadening : ℂ) * Complex.I)⁻¹) *
        (-radialInterbandCurrentAmplitude band e v m p)) = _
  ring

/-- At zero offset and broadening the radial surface spectator is twice the inverse interband gap
multiplying the common radial current amplitude. -/
theorem targetCenteredStredaSurfaceSpectatorCurrentFactor_radial_zero
    (band : Band) (e v m p : ℝ) (hE : energy v m p 0 ≠ 0) :
    targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m p 0 (0, 0) =
      (2 : ℂ) * (((interbandEnergyGap band v m p 0 : ℝ) : ℂ)⁻¹) *
        radialInterbandCurrentAmplitude band e v m p := by
  rw [targetCenteredStredaSurfaceSpectatorCurrentFactor_radial_eq
    band e v m p 0 0 hE]
  simp [two_mul, add_mul]

end

end AnomalousHall.MassiveDirac
