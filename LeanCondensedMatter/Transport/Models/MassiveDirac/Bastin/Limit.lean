import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Bands
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise zero-broadening boundary for the massive-Dirac Bastin kernel

The finite-broadening Bastin decomposition is not allowed to be turned into the clean Hall response
by a pointwise substitution `η = 0`.  Away from the discrete band energies, the retarded and
advanced scalar resolvent coefficients approach the same real-energy resolvent, so their spectral
difference vanishes.  Consequently every fixed-energy band block, and hence the complete
projector-expanded Bastin trace, tends pointwise to zero as the broadening tends to zero.

This is the expected distributional boundary: the nonzero clean Hall response is recovered only
after the energy kernel is paired with an occupation and integrated before the zero-broadening
limit.  The present file deliberately proves only the pointwise statement.  It does not interchange
an energy integral with a limit and it does not introduce a delta-distribution identity.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

private theorem complex_spectral_offset_ne_zero
    (band : Band) (v m px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy band v m px py) :
    (((probeEnergy - bandEnergy band v m px py : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast sub_ne_zero.mpr hprobe

/-- At a probe energy away from the selected band, the scalar projector-resolvent coefficient on
either spectral side tends to the ordinary real-energy coefficient as `η → 0`. -/
theorem tendsto_projectorResolventCoefficient_zero
    (side : SpectralSide) (band : Band) (v m px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy band v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        projectorResolventCoefficient
          (spectralParameter side probeEnergy broadening) band v m px py)
      (nhds 0)
      (nhds (projectorResolventCoefficient (probeEnergy : ℂ) band v m px py)) := by
  have hden :
      spectralParameter side probeEnergy 0 -
          ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0 := by
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
      complex_spectral_offset_ne_zero band v m px py probeEnergy hprobe
  have hcontinuous : ContinuousAt
      (fun broadening : ℝ =>
        spectralParameter side probeEnergy broadening -
          ((bandEnergy band v m px py : ℝ) : ℂ)) 0 := by
    unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  have hinv : Tendsto
      (fun broadening : ℝ =>
        (spectralParameter side probeEnergy broadening -
          ((bandEnergy band v m px py : ℝ) : ℂ))⁻¹)
      (nhds 0)
      (nhds ((spectralParameter side probeEnergy 0 -
        ((bandEnergy band v m px py : ℝ) : ℂ))⁻¹)) :=
    (hcontinuous.inv₀ hden).tendsto
  simpa [projectorResolventCoefficient, spectralParameter, spectralParameterOfRegulator,
    SpectralSide.regulator] using hinv

/-- Off the selected band energy, the retarded-minus-advanced scalar spectral coefficient tends to
zero pointwise. -/
theorem tendsto_spectralDifferenceCoefficient_zero
    (band : Band) (v m px py probeEnergy : ℝ)
    (hprobe : probeEnergy ≠ bandEnergy band v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        spectralDifferenceCoefficient band v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hret := tendsto_projectorResolventCoefficient_zero
    .retarded band v m px py probeEnergy hprobe
  have hadv := tendsto_projectorResolventCoefficient_zero
    .advanced band v m px py probeEnergy hprobe
  simpa only [spectralDifferenceCoefficient, retardedSpectralParameter,
    advancedSpectralParameter, spectralParameter_retarded_ofRegulator,
    spectralParameter_advanced_ofRegulator, sub_self] using hret.sub hadv

/-- A fixed ordered Bastin band-pair contribution tends to zero when the probe energy avoids both
its source and target band energies. -/
theorem tendsto_bastinBandPairContribution_zero
    (source target : Band) (e v m px py probeEnergy : ℝ)
    (hsource : probeEnergy ≠ bandEnergy source v m px py)
    (htarget : probeEnergy ≠ bandEnergy target v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        bastinBandPairContribution source target e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hret := tendsto_projectorResolventCoefficient_zero
    .retarded source v m px py probeEnergy hsource
  have hadv := tendsto_projectorResolventCoefficient_zero
    .advanced source v m px py probeEnergy hsource
  have hdiff := tendsto_spectralDifferenceCoefficient_zero
    target v m px py probeEnergy htarget
  have hretTerm := (((hret.mul hret).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace .x .y source target e v m px py)
      (nhds 0) (nhds (bastinBandBlockTrace .x .y source target e v m px py))))
  have hadvTerm := (((hadv.mul hadv).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace .y .x source target e v m px py)
      (nhds 0) (nhds (bastinBandBlockTrace .y .x source target e v m px py))))
  simpa only [bastinBandPairContribution, pow_two, retardedSpectralParameter,
    advancedSpectralParameter, spectralParameter_retarded_ofRegulator,
    spectralParameter_advanced_ofRegulator, mul_zero, zero_mul, sub_self] using
    hretTerm.sub hadvTerm

/-- The diagonal sector tends pointwise to zero away from both band energies. -/
theorem tendsto_diagonalBastinTraceContribution_zero
    (e v m px py probeEnergy : ℝ)
    (hlower : probeEnergy ≠ bandEnergy .lower v m px py)
    (hupper : probeEnergy ≠ bandEnergy .upper v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        diagonalBastinTraceContribution e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hl := tendsto_bastinBandPairContribution_zero
    .lower .lower e v m px py probeEnergy hlower hlower
  have hu := tendsto_bastinBandPairContribution_zero
    .upper .upper e v m px py probeEnergy hupper hupper
  simpa [diagonalBastinTraceContribution] using hl.add hu

/-- The interband sector also tends pointwise to zero away from both band energies.  Its nonzero
clean Hall weight therefore cannot be recovered by taking the pointwise limit before energy
integration. -/
theorem tendsto_interbandBastinTraceContribution_zero
    (e v m px py probeEnergy : ℝ)
    (hlower : probeEnergy ≠ bandEnergy .lower v m px py)
    (hupper : probeEnergy ≠ bandEnergy .upper v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        interbandBastinTraceContribution e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hlu := tendsto_bastinBandPairContribution_zero
    .lower .upper e v m px py probeEnergy hlower hupper
  have hul := tendsto_bastinBandPairContribution_zero
    .upper .lower e v m px py probeEnergy hupper hlower
  simpa [interbandBastinTraceContribution] using hlu.add hul

/-- Away from the Dirac degeneracy and away from both band energies, the full projector-expanded
Bastin trace tends pointwise to zero as `η → 0`. -/
theorem tendsto_projectorBastinTraceIntegrand_zero
    (e v m px py probeEnergy : ℝ)
    (hE : energy v m px py ≠ 0)
    (hlower : probeEnergy ≠ bandEnergy .lower v m px py)
    (hupper : probeEnergy ≠ bandEnergy .upper v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        projectorBastinTraceIntegrand e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hdiag := tendsto_diagonalBastinTraceContribution_zero
    e v m px py probeEnergy hlower hupper
  have hinter := tendsto_interbandBastinTraceContribution_zero
    e v m px py probeEnergy hlower hupper
  have hsum : Tendsto
      (fun broadening : ℝ =>
        diagonalBastinTraceContribution e v m px py probeEnergy broadening +
          interbandBastinTraceContribution e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
    simpa using hdiag.add hinter
  refine hsum.congr' ?_
  filter_upwards with broadening
  exact (projectorBastinTraceIntegrand_eq_diagonal_add_interband
    e v m px py probeEnergy broadening hE).symm

end

end QuantumTheory.Transport.Models.MassiveDirac
