import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuity of the massive-Dirac Bastin spectator

The target-band Lorentzian kernel depends on the energy offset from the pole and on the spectral
broadening. The opposite-band spectator/current factor is regular wherever the shifted interband
gap stays nonzero.

This file packages the spectator factor in target-centered coordinates, evaluates it at the pole,
proves joint continuity under the general shifted-gap condition, and derives both target-pole and
target-window continuity as corollaries. No compactness bound, energy integration, or momentum
integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The regular interband spectator/current factor written in target-centered coordinates
`(offset, broadening)`. -/
noncomputable def targetCenteredInterbandSpectatorCurrentFactor
    (band : Band) (e v m px py : ℝ) (offsetBroadening : ℝ × ℝ) : ℂ :=
  interbandSpectatorCurrentFactor band e v m px py
    (bandEnergy band v m px py + offsetBroadening.1) offsetBroadening.2

/-- At zero offset and zero broadening, the regular factor is exactly the inverse-gap-squared
antisymmetric current block. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) :
    targetCenteredInterbandSpectatorCurrentFactor band e v m px py (0, 0) =
      (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
        ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py) := by
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  simp [retardedSpectralParameter, advancedSpectralParameter, spectralParameterOfRegulator,
    projectorResolventCoefficient_oppositeBand_at_bandEnergy]

/-- If the real shifted interband gap is nonzero at an offset, then the target-centered regular
spectator/current factor is jointly continuous there for arbitrary real broadening. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
    (band : Band) (e v m px py : ℝ) (p : ℝ × ℝ)
    (hshift : interbandEnergyGap band v m px py + p.1 ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      p := by
  have hside : ∀ side : SpectralSide, ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy band v m px py + q.1) q.2)
          (oppositeBand band) v m px py)
      p := by
    intro side
    have hparameter : ContinuousAt
        (fun q : ℝ × ℝ =>
          spectralParameter side (bandEnergy band v m px py + q.1) q.2)
        p := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hden :
        spectralParameter side (bandEnergy band v m px py + p.1) p.2 -
            ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ) ≠ 0 := by
      intro hzero
      have hre :
          bandEnergy band v m px py + p.1 -
            bandEnergy (oppositeBand band) v m px py = 0 := by
        simpa [spectralParameter, spectralParameterOfRegulator] using congrArg Complex.re hzero
      apply hshift
      unfold interbandEnergyGap
      linarith
    change ContinuousAt
      (fun q : ℝ × ℝ =>
        (spectralParameter side (bandEnergy band v m px py + q.1) q.2 -
          ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))⁻¹)
      p
    exact (hparameter.sub continuousAt_const).inv₀ hden
  have hret : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
          (oppositeBand band) v m px py)
      p := by
    simpa only [spectralParameter_retarded] using hside .retarded
  have hadv : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
          (oppositeBand band) v m px py)
      p := by
    simpa only [spectralParameter_advanced] using hside .advanced
  have hxy := (hret.mul hret).mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py) p)
  have hyx := (hadv.mul hadv).mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py) p)
  have hsub := hxy.sub hyx
  change ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
              (retardedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
              (oppositeBand band) v m px py *
            projectorResolventCoefficient
              (retardedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
              (oppositeBand band) v m px py *
          bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
        projectorResolventCoefficient
              (advancedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
              (oppositeBand band) v m px py *
            projectorResolventCoefficient
              (advancedSpectralParameter (bandEnergy band v m px py + q.1) q.2)
              (oppositeBand band) v m px py *
          bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)
      p at hsub
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  dsimp
  simpa [pow_two] using hsub

/-- Away from the Dirac degeneracy, the target-centered spectator/current factor is jointly
continuous in energy offset and broadening at the target pole. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      (0, 0) := by
  apply continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
  simpa using interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE

/-- Jointly sending both the target-centered energy offset and broadening to zero extracts the same
inverse-gap-squared antisymmetric current block as the fixed-energy pole limit. -/
theorem tendsto_targetCenteredInterbandSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
      (nhds (0, 0))
      (nhds
        (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
            bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
          ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
            bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)) := by
  have h := (continuousAt_targetCenteredInterbandSpectatorCurrentFactor_zero
    band e v m px py hE).tendsto
  rw [targetCenteredInterbandSpectatorCurrentFactor_zero band e v m px py] at h
  exact h

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
