import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac interband Bastin pole factor

For a target band `n`, the interband Bastin pair has source band `oppositeBand n`.  Its scalar
retarded-minus-advanced factor is the Lorentzian pole centered at `E_n`; the remaining retarded and
advanced opposite-band resolvent squares are regular spectators multiplying the two current-trace
orderings.

This file separates those pieces exactly and proves the regular spectator/current factor converges
at the target-band pole to the inverse-gap-squared antisymmetric current block.  Together with the
Berry numerator bridge, this is the local coefficient that the occupation-weighted Lorentzian
energy integral must extract next.

No energy integration or momentum integration is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Model-local shorthand for the generic Lorentzian spectral kernel used throughout the Bastin
pole chain. -/
abbrev lorentzianSpectralKernel := QuantumTheory.Transport.lorentzianSpectralKernel

/-- The scalar spectral difference in the two-band Bastin decomposition is exactly a Lorentzian
centered at the selected band energy. -/
theorem spectralDifferenceCoefficient_eq_lorentzian
    (band : Band) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralDifferenceCoefficient band v m px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy band v m px py) broadening : ℂ) := by
  unfold spectralDifferenceCoefficient projectorResolventCoefficient
    retardedSpectralParameter advancedSpectralParameter spectralParameterOfRegulator
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    inv_add_I_sub_inv_sub_I_eq_lorentzian
      (probeEnergy - bandEnergy band v m px py) broadening hbroadening

/-- The regular current factor multiplying the target-band Lorentzian pole in an interband Bastin
pair.  The source band is fixed to the opposite band. -/
noncomputable def interbandSpectatorCurrentFactor
    (band : Band) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening)
    (oppositeBand band) v m px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening)
    (oppositeBand band) v m px py
  r ^ 2 * bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
    a ^ 2 * bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py

/-- Exact factorization of one interband Bastin pair into its Lorentzian spectral pole and regular
spectator/current factor. -/
theorem bastinBandPairContribution_opposite_source_eq_lorentzian
    (band : Band) (e v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    bastinBandPairContribution (oppositeBand band) band
        e v m px py probeEnergy broadening =
      (-2 * Complex.I) *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy band v m px py) broadening : ℂ) *
        interbandSpectatorCurrentFactor
          band e v m px py probeEnergy broadening := by
  unfold bastinBandPairContribution interbandSpectatorCurrentFactor
  dsimp
  rw [spectralDifferenceCoefficient_eq_lorentzian
    band v m px py probeEnergy broadening hbroadening]
  ring

/-- At the target-band pole, the regular spectator/current factor converges to the inverse squared
interband gap multiplying the antisymmetric current block. -/
theorem tendsto_interbandSpectatorCurrentFactor_at_bandPole
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        interbandSpectatorCurrentFactor
          band e v m px py (bandEnergy band v m px py) broadening)
      (nhds 0)
      (nhds
        (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
            bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py -
          ((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
            bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)) := by
  have hret := tendsto_retarded_oppositeBandCoefficient_sq_at_bandPole
    band v m px py hE
  have hadv := tendsto_advanced_oppositeBandCoefficient_sq_at_bandPole
    band v m px py hE
  have hxy := hret.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py)
      (nhds 0)
      (nhds (bastinBandBlockTrace .x .y (oppositeBand band) band e v m px py)))
  have hyx := hadv.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)
      (nhds 0)
      (nhds (bastinBandBlockTrace .y .x (oppositeBand band) band e v m px py)))
  simpa [interbandSpectatorCurrentFactor] using hxy.sub hyx

end

end AnomalousHall.MassiveDirac
