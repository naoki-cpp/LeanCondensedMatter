import LeanCondensedMatter.Models.MassiveDirac.Bastin.Bands
import Mathlib.Topology.Algebra.GroupWithZero

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

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- A fixed direction-indexed ordered Bastin band-pair contribution tends to zero when the probe
energy avoids both its source and target band energies. -/
theorem tendsto_bastinBandPairContribution_zero
    (μ ν : Fin 2) (source target : Band) (e v m px py probeEnergy : ℝ)
    (hsource : probeEnergy ≠ bandEnergy source v m px py)
    (htarget : probeEnergy ≠ bandEnergy target v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        bastinBandPairContribution μ ν source target e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  have hret := tendsto_scalarResolventCoefficient_spectralParameter_zero
    .retarded probeEnergy (bandEnergy source v m px py) hsource
  have hadv := tendsto_scalarResolventCoefficient_spectralParameter_zero
    .advanced probeEnergy (bandEnergy source v m px py) hsource
  have hdiff := tendsto_scalarSpectralDifferenceCoefficient_zero
    (bandEnergy target v m px py) probeEnergy htarget
  have hretTerm := (((hret.mul hret).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => currentBandBlockTrace μ ν source target e v m px py)
      (nhds 0) (nhds (currentBandBlockTrace μ ν source target e v m px py))))
  have hadvTerm := (((hadv.mul hadv).mul hdiff).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => currentBandBlockTrace ν μ source target e v m px py)
      (nhds 0) (nhds (currentBandBlockTrace ν μ source target e v m px py))))
  simpa only [bastinBandPairContribution, pow_two, retardedSpectralParameter,
    advancedSpectralParameter, spectralParameter_retarded_ofRegulator,
    spectralParameter_advanced_ofRegulator, mul_zero, zero_mul, sub_self] using
    hretTerm.sub hadvTerm

/-- The diagonal Hall sector tends pointwise to zero away from both band energies. -/
theorem tendsto_diagonalBastinTraceContribution_zero
    (e v m px py probeEnergy : ℝ)
    (hlower : probeEnergy ≠ bandEnergy .lower v m px py)
    (hupper : probeEnergy ≠ bandEnergy .upper v m px py) :
    Tendsto
      (fun broadening : ℝ =>
        diagonalBastinTraceContribution e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
  simpa only [diagonalBastinTraceContribution, Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun band _ =>
      tendsto_bastinBandPairContribution_zero 0 1 band band e v m px py probeEnergy
        (by cases band <;> assumption) (by cases band <;> assumption)))

/-- The interband Hall sector also tends pointwise to zero away from both band energies. Its nonzero
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
  simpa only [interbandBastinTraceContribution, Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun band _ =>
      tendsto_bastinBandPairContribution_zero 0 1 band (oppositeBand band)
        e v m px py probeEnergy
        (by cases band <;> assumption) (by cases band <;> assumption)))

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
  have hsum : Tendsto
      (fun broadening : ℝ =>
        diagonalBastinTraceContribution e v m px py probeEnergy broadening +
          interbandBastinTraceContribution e v m px py probeEnergy broadening)
      (nhds 0) (nhds 0) := by
    simpa using
      (tendsto_diagonalBastinTraceContribution_zero
        e v m px py probeEnergy hlower hupper).add
      (tendsto_interbandBastinTraceContribution_zero
        e v m px py probeEnergy hlower hupper)
  refine hsum.congr' ?_
  filter_upwards with broadening
  exact (projectorBastinTraceIntegrand_eq_diagonal_add_interband
    e v m px py probeEnergy broadening hE).symm

end

end QuantumTheory.Models.MassiveDirac
