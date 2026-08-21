import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfacePoleFactor
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuity of the massive-Dirac Středa surface spectator

The target-band Středa surface pole is Lorentzian, while the opposite-band spectator remains regular
near `(offset, broadening) = (0, 0)`.  This file gives the exact pole value and joint continuity
needed by the following Lorentzian approximate-identity step, and extends that continuity over any
target-centered strip that stays away from the opposite-band pole.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Exact value of the target-centered Středa surface spectator at the clean target-band pole. -/
theorem targetCenteredStredaSurfaceSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) :
    targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py (0, 0) =
      ((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
          bastinXYBandBlockTrace (oppositeBand band) band e v m px py -
        ((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
          bastinYXBandBlockTrace (oppositeBand band) band e v m px py := by
  unfold targetCenteredStredaSurfaceSpectatorCurrentFactor
    stredaSurfaceSpectatorCurrentFactor
  simp [retardedSpectralParameter, advancedSpectralParameter,
    projectorResolventCoefficient_oppositeBand_at_bandEnergy]

/-- Away from the Dirac degeneracy, the target-centered surface spectator is jointly continuous in
energy offset and broadening at the target pole. -/
theorem continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ContinuousAt
      (targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py)
      (0, 0) := by
  have hgap : interbandEnergyGap band v m px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hgapc : (((interbandEnergyGap band v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hgap
  have hretDen : ContinuousAt
      (fun p : ℝ × ℝ =>
        (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))
      (0, 0) := by
    fun_prop
  have hretDen_ne :
      (((bandEnergy band v m px py + (0 : ℝ) : ℝ) : ℂ) + (0 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ) ≠ 0 := by
    simpa [interbandEnergyGap] using hgapc
  have hadvDen : ContinuousAt
      (fun p : ℝ × ℝ =>
        (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) - (p.2 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))
      (0, 0) := by
    fun_prop
  have hadvDen_ne :
      (((bandEnergy band v m px py + (0 : ℝ) : ℝ) : ℂ) - (0 : ℂ) * Complex.I) -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ) ≠ 0 := by
    simpa [interbandEnergyGap] using hgapc
  have hret : ContinuousAt
      (fun p : ℝ × ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py + p.1) p.2)
          (oppositeBand band) v m px py)
      (0, 0) := by
    simpa [projectorResolventCoefficient, retardedSpectralParameter] using
      hretDen.inv₀ hretDen_ne
  have hadv : ContinuousAt
      (fun p : ℝ × ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py + p.1) p.2)
          (oppositeBand band) v m px py)
      (0, 0) := by
    simpa [projectorResolventCoefficient, advancedSpectralParameter] using
      hadvDen.inv₀ hadvDen_ne
  have hxy := hret.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinXYBandBlockTrace (oppositeBand band) band e v m px py)
      (0, 0))
  have hyx := hadv.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinYXBandBlockTrace (oppositeBand band) band e v m px py)
      (0, 0))
  unfold targetCenteredStredaSurfaceSpectatorCurrentFactor
    stredaSurfaceSpectatorCurrentFactor
  dsimp
  simpa using hxy.sub hyx

/-- Joint convergence of the target-centered Středa surface spectator to its clean pole value. -/
theorem tendsto_targetCenteredStredaSurfaceSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py)
      (nhds (0, 0))
      (nhds
        (((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
            bastinXYBandBlockTrace (oppositeBand band) band e v m px py -
          ((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
            bastinYXBandBlockTrace (oppositeBand band) band e v m px py)) := by
  have h :=
    (continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_zero
      band e v m px py hE).tendsto
  rw [targetCenteredStredaSurfaceSpectatorCurrentFactor_zero band e v m px py] at h
  exact h

/-- If the shifted real interband gap is nonzero, the surface spectator is continuous at that
arbitrary target-centered offset and broadening. -/
theorem continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_of_shiftedGap_ne_zero
    (band : Band) (e v m px py : ℝ) (p : ℝ × ℝ)
    (hshift : interbandEnergyGap band v m px py + p.1 ≠ 0) :
    ContinuousAt
      (targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py)
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
  have hxy := hret.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinXYBandBlockTrace (oppositeBand band) band e v m px py) p)
  have hyx := hadv.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ => bastinYXBandBlockTrace (oppositeBand band) band e v m px py) p)
  unfold targetCenteredStredaSurfaceSpectatorCurrentFactor
    stredaSurfaceSpectatorCurrentFactor
  dsimp
  simpa using hxy.sub hyx

/-- A target-centered window narrower than the interband gap is a continuity region for the surface
spectator, independently of the broadening coordinate. -/
theorem continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_on_targetWindow
    (band : Band) (e v m px py radius : ℝ) (p : ℝ × ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|)
    (hoffset : |p.1| ≤ radius) :
    ContinuousAt
      (targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py)
      p := by
  apply continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_of_shiftedGap_ne_zero
  exact interbandEnergyGap_add_offset_ne_zero_on_targetWindow
    band v m px py p.1 radius hradius hoffset

/-- The full target-centered strip cut out by a window narrower than the interband gap is a
continuity region for the Středa surface spectator. -/
theorem continuousOn_targetCenteredStredaSurfaceSpectatorCurrentFactor_targetStrip
    (band : Band) (e v m px py radius : ℝ)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    ContinuousOn
      (targetCenteredStredaSurfaceSpectatorCurrentFactor band e v m px py)
      {p : ℝ × ℝ | |p.1| ≤ radius} := by
  intro p hp
  exact
    (continuousAt_targetCenteredStredaSurfaceSpectatorCurrentFactor_on_targetWindow
      band e v m px py radius p hradius hp).continuousWithinAt

end

end AnomalousHall.MassiveDirac
