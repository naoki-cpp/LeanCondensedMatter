import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Interband
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Spectator
import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Rashba-exchange interband Bastin pole factor

An opposite-source interband Bastin pair factors into the target-band Lorentzian pole and a regular
spectator/current factor.  At the target pole the latter tends to the inverse-gap-squared
antisymmetric current block.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

theorem spectralDifferenceCoefficient_eq_lorentzian
    (params : Parameters) (band : Band) (px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralDifferenceCoefficient params band px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy params band px py) broadening : ℂ) := by
  unfold spectralDifferenceCoefficient projectorResolventCoefficient
    retardedSpectralParameter advancedSpectralParameter
  rw [spectralParameter_retarded_ofRegulator, spectralParameter_advanced_ofRegulator]
  unfold spectralParameterOfRegulator
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - bandEnergy params band px py) broadening hbroadening

/-- Regular current factor multiplying the target-band Lorentzian pole. -/
noncomputable def interbandSpectatorCurrentFactor
    (params : Parameters) (μ ν : Fin 2) (band : Band)
    (px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening)
    params (oppositeBand band) px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening)
    params (oppositeBand band) px py
  r ^ 2 * bastinBandBlockTrace params μ ν (oppositeBand band) band px py -
    a ^ 2 * bastinBandBlockTrace params ν μ (oppositeBand band) band px py

theorem bastinBandPairContribution_opposite_source_eq_lorentzian
    (params : Parameters) (μ ν : Fin 2) (band : Band)
    (px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    bastinBandPairContribution params μ ν (oppositeBand band) band
        px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy params band px py) broadening : ℂ) *
        interbandSpectatorCurrentFactor params μ ν band
          px py probeEnergy broadening := by
  unfold bastinBandPairContribution interbandSpectatorCurrentFactor
  dsimp
  rw [spectralDifferenceCoefficient_eq_lorentzian
    params band px py probeEnergy broadening hbroadening]
  ring

theorem tendsto_interbandSpectatorCurrentFactor_at_bandPole
    (params : Parameters) (μ ν : Fin 2) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        interbandSpectatorCurrentFactor params μ ν band
          px py (bandEnergy params band px py) broadening)
      (nhds 0)
      (nhds
        (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinInterbandBlockDifference params μ ν band px py)) := by
  have hret : Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (retardedSpectralParameter
            (bandEnergy params band px py) broadening)
          params (oppositeBand band) px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
    simpa only [retardedSpectralParameter] using
      tendsto_oppositeBandCoefficient_sq_at_bandPole
        .retarded params band px py hE
  have hadv : Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (advancedSpectralParameter
            (bandEnergy params band px py) broadening)
          params (oppositeBand band) px py ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
    simpa only [advancedSpectralParameter] using
      tendsto_oppositeBandCoefficient_sq_at_bandPole
        .advanced params band px py hE
  have hμν := hret.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ =>
        bastinBandBlockTrace params μ ν (oppositeBand band) band px py)
      (nhds 0)
      (nhds (bastinBandBlockTrace params μ ν (oppositeBand band) band px py)))
  have hνμ := hadv.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ =>
        bastinBandBlockTrace params ν μ (oppositeBand band) band px py)
      (nhds 0)
      (nhds (bastinBandBlockTrace params ν μ (oppositeBand band) band px py)))
  simpa [interbandSpectatorCurrentFactor, bastinInterbandBlockDifference, mul_sub] using
    hμν.sub hνμ

end

end QuantumTheory.Transport.Models.RashbaExchange
