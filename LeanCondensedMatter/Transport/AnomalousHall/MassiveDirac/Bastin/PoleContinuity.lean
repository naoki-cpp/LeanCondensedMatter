import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Joint continuity of the massive-Dirac Bastin spectator at a target pole

The target-band Lorentzian kernel depends on the energy offset from the pole and on the spectral
broadening.  The opposite-band spectator/current factor is regular in both variables near the
point `(offset, broadening) = (0, 0)` because the interband gap is nonzero away from the Dirac
degeneracy.

This file packages the spectator factor in target-centered coordinates, evaluates it at the pole,
and proves joint continuity there.  This is the topological input needed for the local error term in
the occupation-weighted Lorentzian integral.  No energy integration or momentum integration is
performed here.
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
  simp [retardedSpectralParameter, advancedSpectralParameter,
    projectorResolventCoefficient_oppositeBand_at_bandEnergy]

/-- Away from the Dirac degeneracy, the target-centered spectator/current factor is jointly
continuous in energy offset and broadening at the target pole. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_zero
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
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
  have hretSq := hret.mul hret
  have hadvSq := hadv.mul hadv
  have hxy := hretSq.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py)
      (0, 0))
  have hyx := hadvSq.mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)
      (0, 0))
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  dsimp
  simpa [pow_two] using hxy.sub hyx

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

end

end AnomalousHall.MassiveDirac
