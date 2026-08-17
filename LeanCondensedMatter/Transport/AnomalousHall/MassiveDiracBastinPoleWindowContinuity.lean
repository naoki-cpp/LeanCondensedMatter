import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleContinuity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuity of the Bastin spectator across a target-centered window

The previous pole theorem proves joint continuity of the regular interband spectator/current factor
at `(offset, broadening) = (0, 0)`.  For the occupation-weighted pole integral we also need the
factor to stay regular throughout a fixed target-centered energy window.

The target-window separation theorem already shows that a window with radius smaller than the
interband gap cannot reach the opposite-band source pole.  This file turns that separation into
continuity of the spectator/current factor at every point of the corresponding offset strip.

No compactness bound, energy integration, or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- If the real shifted interband gap is nonzero at an offset, then the target-centered regular
spectator/current factor is jointly continuous there for arbitrary real broadening. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
    (band : Band) (e v m px py : ℝ) (p : ℝ × ℝ)
    (hshift : interbandEnergyGap band v m px py + p.1 ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      p := by
  have hretDen : ContinuousAt
      (fun q : ℝ × ℝ =>
        (((bandEnergy band v m px py + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))
      p := by
    fun_prop
  have hretDen_ne :
      (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ) ≠ 0 := by
    intro hzero
    have hre :
        bandEnergy band v m px py + p.1 -
          bandEnergy (oppositeBand band) v m px py = 0 := by
      simpa using congrArg Complex.re hzero
    apply hshift
    unfold interbandEnergyGap
    linarith
  have hadvDen : ContinuousAt
      (fun q : ℝ × ℝ =>
        (((bandEnergy band v m px py + q.1 : ℝ) : ℂ) - (q.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))
      p := by
    fun_prop
  have hadvDen_ne :
      (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) - (p.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ) ≠ 0 := by
    intro hzero
    have hre :
        bandEnergy band v m px py + p.1 -
          bandEnergy (oppositeBand band) v m px py = 0 := by
      simpa using congrArg Complex.re hzero
    apply hshift
    unfold interbandEnergyGap
    linarith
  have hret : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
          (oppositeBand band) v m px py)
      p := by
    simpa [projectorResolventCoefficient, retardedSpectralParameter] using
      hretDen.inv₀ hretDen_ne
  have hadv : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
          (oppositeBand band) v m px py)
      p := by
    simpa [projectorResolventCoefficient, advancedSpectralParameter] using
      hadvDen.inv₀ hadvDen_ne
  have hretSq := hret.mul hret
  have hadvSq := hadv.mul hadv
  have hxy := hretSq.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinXYBandBlockTrace (oppositeBand band) band e v m px py) p)
  have hyx := hadvSq.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinYXBandBlockTrace (oppositeBand band) band e v m px py) p)
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  dsimp
  simpa [pow_two] using hxy.sub hyx

/-- A target-centered energy window narrower than the interband gap is a continuity region for the
regular spectator/current factor, independently of the broadening coordinate. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_on_targetWindow
    (band : Band) (e v m px py radius : ℝ) (p : ℝ × ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |p.1| ≤ radius) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      p := by
  apply continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
  exact interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    band v m px py p.1 radius hradius hoffset

/-- On the full broadening-unrestricted strip cut out by a target-centered energy window narrower
than the interband gap, the regular spectator/current factor is continuous. -/
theorem continuousOn_targetCenteredInterbandSpectatorCurrentFactor_targetStrip
    (band : Band) (e v m px py radius : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ContinuousOn
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      {p : ℝ × ℝ | |p.1| ≤ radius} := by
  intro p hp
  exact (continuousAt_targetCenteredInterbandSpectatorCurrentFactor_on_targetWindow
    band e v m px py radius p hradius hp).continuousWithinAt

end

end AnomalousHall.MassiveDirac
