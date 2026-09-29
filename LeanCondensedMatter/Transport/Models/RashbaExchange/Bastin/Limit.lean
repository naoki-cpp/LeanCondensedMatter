import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Bands
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise zero-broadening boundary for the Rashba-exchange Bastin kernel

Away from both band energies, each finite-band Bastin contribution tends pointwise to zero as the
broadening tends to zero.  The nonzero clean Hall weight is therefore distributional in energy and
must be extracted only after energy integration.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

private theorem complex_spectral_offset_ne_zero
    (params : Parameters) (band : Band) (px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy params band px py) :
    (((probeEnergy - bandEnergy params band px py : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast sub_ne_zero.mpr hprobe

theorem tendsto_projectorResolventCoefficient_zero
    (side : SpectralSide) (params : Parameters) (band : Band)
    (px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy params band px py) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side probeEnergy broadening) params band px py)
      (nhds 0)
      (nhds (projectorResolventCoefficient (probeEnergy : ℂ) params band px py)) := by
  have hden :
      spectralParameter side probeEnergy 0 -
          ((bandEnergy params band px py : ℝ) : ℂ) ≠ 0 := by
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
      complex_spectral_offset_ne_zero params band px py probeEnergy hprobe
  have hcontinuous : ContinuousAt
      (fun broadening : ℝ =>
        spectralParameter side probeEnergy broadening -
          ((bandEnergy params band px py : ℝ) : ℂ)) 0 := by
    unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  have hinv : Tendsto
      (fun broadening : ℝ =>
        (spectralParameter side probeEnergy broadening -
          ((bandEnergy params band px py : ℝ) : ℂ))⁻¹)
      (nhds 0)
      (nhds ((spectralParameter side probeEnergy 0 -
        ((bandEnergy params band px py : ℝ) : ℂ))⁻¹)) :=
    (hcontinuous.inv₀ hden).tendsto
  simpa [projectorResolventCoefficient, spectralParameter, spectralParameterOfRegulator,
    SpectralSide.regulator] using hinv

theorem tendsto_spectralDifferenceCoefficient_zero
    (params : Parameters) (band : Band) (px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy params band px py) :
    Tendsto
      (fun broadening : ℝ =>
        spectralDifferenceCoefficient params band px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hret := tendsto_projectorResolventCoefficient_zero
    .retarded params band px py probeEnergy hprobe
  have hadv := tendsto_projectorResolventCoefficient_zero
    .advanced params band px py probeEnergy hprobe
  simpa only [spectralDifferenceCoefficient, retardedSpectralParameter,
    advancedSpectralParameter, spectralParameter_retarded_ofRegulator,
    spectralParameter_advanced_ofRegulator, sub_self] using hret.sub hadv

theorem tendsto_bastinBandPairContribution_zero
    (params : Parameters) (μ ν : Fin 2) (source target : Band)
    (px py probeEnergy : ℝ)
    (hsource : probeEnergy ≠ bandEnergy params source px py)
    (htarget : probeEnergy ≠ bandEnergy params target px py) :
    Tendsto
      (fun broadening : ℝ =>
        bastinBandPairContribution params μ ν source target
          px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hret := tendsto_projectorResolventCoefficient_zero
    .retarded params source px py probeEnergy hsource
  have hadv := tendsto_projectorResolventCoefficient_zero
    .advanced params source px py probeEnergy hsource
  have hdiff := tendsto_spectralDifferenceCoefficient_zero
    params target px py probeEnergy htarget
  have hretTerm := (((hret.mul hret).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace params μ ν source target px py)
      (nhds 0) (nhds (bastinBandBlockTrace params μ ν source target px py))))
  have hadvTerm := (((hadv.mul hadv).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace params ν μ source target px py)
      (nhds 0) (nhds (bastinBandBlockTrace params ν μ source target px py))))
  simpa only [bastinBandPairContribution, pow_two, retardedSpectralParameter,
    advancedSpectralParameter, spectralParameter_retarded_ofRegulator,
    spectralParameter_advanced_ofRegulator, mul_zero, zero_mul, sub_self] using
    hretTerm.sub hadvTerm

end

end QuantumTheory.Transport.Models.RashbaExchange
