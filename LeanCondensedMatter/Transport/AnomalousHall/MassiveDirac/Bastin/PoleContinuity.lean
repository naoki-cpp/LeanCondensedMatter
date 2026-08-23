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
  let ret : ℝ × ℝ → ℂ := fun p =>
    projectorResolventCoefficient
      (retardedSpectralParameter (bandEnergy band v m px py + p.1) p.2)
      (oppositeBand band) v m px py
  let adv : ℝ × ℝ → ℂ := fun p =>
    projectorResolventCoefficient
      (advancedSpectralParameter (bandEnergy band v m px py + p.1) p.2)
      (oppositeBand band) v m px py
  have hret : ContinuousAt ret (0, 0) := by
    have h := hretDen.inv₀ hretDen_ne
    have hfun :
        (fun p : ℝ × ℝ =>
          (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) -
            ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))⁻¹ =
          (fun p : ℝ × ℝ =>
            ((((bandEnergy band v m px py + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) -
              ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))⁻¹) := by
      funext p
      rfl
    rw [hfun] at h
    simpa [ret, projectorResolventCoefficient, retardedSpectralParameter] using h
  have hadv : ContinuousAt adv (0, 0) := by
    have h := hadvDen.inv₀ hadvDen_ne
    have hfun :
        (fun p : ℝ × ℝ =>
          (((bandEnergy band v m px py + p.1 : ℝ) : ℂ) - (p.2 : ℂ) * Complex.I) -
            ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))⁻¹ =
          (fun p : ℝ × ℝ =>
            ((((bandEnergy band v m px py + p.1 : ℝ) : ℂ) - (p.2 : ℂ) * Complex.I) -
              ((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ))⁻¹) := by
      funext p
      rfl
    rw [hfun] at h
    simpa [adv, projectorResolventCoefficient, advancedSpectralParameter] using h
  have hretSqRaw := hret.mul hret
  have hretSq : ContinuousAt (fun p => ret p * ret p) (0, 0) := by
    have hfun : ret * ret = (fun p => ret p * ret p) := by
      funext p
      rfl
    rw [hfun] at hretSqRaw
    exact hretSqRaw
  have hadvSqRaw := hadv.mul hadv
  have hadvSq : ContinuousAt (fun p => adv p * adv p) (0, 0) := by
    have hfun : adv * adv = (fun p => adv p * adv p) := by
      funext p
      rfl
    rw [hfun] at hadvSqRaw
    exact hadvSqRaw
  let xy : ℂ := bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py
  let yx : ℂ := bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py
  have hxyRaw := hretSq.mul
    (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => xy) (0, 0))
  have hxy : ContinuousAt (fun p => ret p * ret p * xy) (0, 0) := by
    have hfun :
        (fun p => ret p * ret p) * (fun _ : ℝ × ℝ => xy) =
          (fun p => ret p * ret p * xy) := by
      funext p
      rfl
    rw [hfun] at hxyRaw
    exact hxyRaw
  have hyxRaw := hadvSq.mul
    (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => yx) (0, 0))
  have hyx : ContinuousAt (fun p => adv p * adv p * yx) (0, 0) := by
    have hfun :
        (fun p => adv p * adv p) * (fun _ : ℝ × ℝ => yx) =
          (fun p => adv p * adv p * yx) := by
      funext p
      rfl
    rw [hfun] at hyxRaw
    exact hyxRaw
  have hsubRaw := hxy.sub hyx
  have hsub : ContinuousAt
      (fun p => ret p * ret p * xy - adv p * adv p * yx) (0, 0) := by
    have hfun :
        (fun p => ret p * ret p * xy) - (fun p => adv p * adv p * yx) =
          (fun p => ret p * ret p * xy - adv p * adv p * yx) := by
      funext p
      rfl
    rw [hfun] at hsubRaw
    exact hsubRaw
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  dsimp
  simpa [ret, adv, xy, yx] using hsub

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
