import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleWindow
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Continuity of the Rashba-exchange Bastin spectator

The target-centered interband spectator/current factor is jointly continuous wherever the shifted
opposite-band gap is nonzero.  This is the model-specific regularity input consumed by the generic
Lorentzian pole-extraction theorem.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

/-- Hall interband spectator/current factor in target-centered coordinates. -/
noncomputable def targetCenteredInterbandSpectatorCurrentFactor
    (params : Parameters) (band : Band) (px py : ℝ)
    (offsetBroadening : ℝ × ℝ) : ℂ :=
  interbandSpectatorCurrentFactor params 0 1 band px py
    (bandEnergy params band px py + offsetBroadening.1) offsetBroadening.2

/-- At the target pole the regular factor is the inverse-gap-squared antisymmetric current block. -/
theorem targetCenteredInterbandSpectatorCurrentFactor_zero
    (params : Parameters) (band : Band) (px py : ℝ) :
    targetCenteredInterbandSpectatorCurrentFactor params band px py (0, 0) =
      (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2 *
        bastinInterbandBlockDifference params 0 1 band px py) := by
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  simp [retardedSpectralParameter, advancedSpectralParameter,
    spectralParameterOfRegulator,
    projectorResolventCoefficient_oppositeBand_at_bandEnergy,
    bastinInterbandBlockDifference, mul_sub]

/-- Joint continuity of the regular spectator/current factor away from the shifted source pole. -/
theorem continuousAt_targetCenteredInterbandSpectatorCurrentFactor_of_shiftedGap_ne_zero
    (params : Parameters) (band : Band) (px py : ℝ) (p : ℝ × ℝ)
    (hshift : interbandEnergyGap params band px py + p.1 ≠ 0) :
    ContinuousAt
      (targetCenteredInterbandSpectatorCurrentFactor params band px py)
      p := by
  have hside : ∀ side : SpectralSide, ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (spectralParameter side (bandEnergy params band px py + q.1) q.2)
          params (oppositeBand band) px py)
      p := by
    intro side
    have hparameter : ContinuousAt
        (fun q : ℝ × ℝ =>
          spectralParameter side (bandEnergy params band px py + q.1) q.2)
        p := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    have hden :
        spectralParameter side (bandEnergy params band px py + p.1) p.2 -
            ((bandEnergy params (oppositeBand band) px py : ℝ) : ℂ) ≠ 0 := by
      intro hzero
      have hre :
          bandEnergy params band px py + p.1 -
            bandEnergy params (oppositeBand band) px py = 0 := by
        simpa [spectralParameter, spectralParameterOfRegulator] using
          congrArg Complex.re hzero
      apply hshift
      unfold interbandEnergyGap
      linarith
    change ContinuousAt
      (fun q : ℝ × ℝ =>
        (spectralParameter side (bandEnergy params band px py + q.1) q.2 -
          ((bandEnergy params (oppositeBand band) px py : ℝ) : ℂ))⁻¹)
      p
    exact (hparameter.sub continuousAt_const).inv₀ hden
  have hret : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter (bandEnergy params band px py + q.1) q.2)
          params (oppositeBand band) px py)
      p := by
    simpa only [retardedSpectralParameter] using hside .retarded
  have hadv : ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter (bandEnergy params band px py + q.1) q.2)
          params (oppositeBand band) px py)
      p := by
    simpa only [advancedSpectralParameter] using hside .advanced
  have hxy := (hret.mul hret).mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace params 0 1 (oppositeBand band) band px py) p)
  have hyx := (hadv.mul hadv).mul
    (continuousAt_const : ContinuousAt
      (fun _ : ℝ × ℝ =>
        bastinBandBlockTrace params 1 0 (oppositeBand band) band px py) p)
  have hsub := hxy.sub hyx
  change ContinuousAt
      (fun q : ℝ × ℝ =>
        projectorResolventCoefficient
              (retardedSpectralParameter
                (bandEnergy params band px py + q.1) q.2)
              params (oppositeBand band) px py *
            projectorResolventCoefficient
              (retardedSpectralParameter
                (bandEnergy params band px py + q.1) q.2)
              params (oppositeBand band) px py *
          bastinBandBlockTrace params 0 1 (oppositeBand band) band px py -
        projectorResolventCoefficient
              (advancedSpectralParameter
                (bandEnergy params band px py + q.1) q.2)
              params (oppositeBand band) px py *
            projectorResolventCoefficient
              (advancedSpectralParameter
                (bandEnergy params band px py + q.1) q.2)
              params (oppositeBand band) px py *
          bastinBandBlockTrace params 1 0 (oppositeBand band) band px py)
      p at hsub
  unfold targetCenteredInterbandSpectatorCurrentFactor interbandSpectatorCurrentFactor
  dsimp
  simpa [pow_two] using hsub

end

end QuantumTheory.Transport.Models.RashbaExchange
