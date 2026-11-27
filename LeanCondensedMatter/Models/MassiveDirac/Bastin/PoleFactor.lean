import LeanCondensedMatter.Models.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.QuantumTheory.TwoBand
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Massive-Dirac interband Bastin pole factor

For a target band `n`, the interband Bastin pair has source band `oppositeBand n`. Its scalar
retarded-minus-advanced factor is the Lorentzian pole centered at `E_n`; the remaining retarded and
advanced opposite-band resolvent squares are regular spectators multiplying the two current-trace
orderings.

This file separates those pieces exactly while keeping the current directions generic, and
expresses the opposite-band resolvent in target-centered offset coordinates for downstream Hall
continuity and radial estimates. At the target-band pole the regular spectator/current factor
converges to the inverse-gap-squared antisymmetric current block.

No energy integration or momentum integration is performed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport QuantumTheory.TwoBand

open Filter

/-- The regular current factor multiplying the target-band Lorentzian pole in an interband Bastin
pair for an ordered current-direction pair `(μ,ν)`. The source band is fixed to the opposite band. -/
noncomputable def interbandSpectatorCurrentFactor
    (μ ν : Fin 2) (band : TwoBand) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  let r := scalarResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening)
    (bandEnergy (oppositeBand band) v m px py)
  let a := scalarResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening)
    (bandEnergy (oppositeBand band) v m px py)
  r ^ 2 * currentBandBlockTrace μ ν (oppositeBand band) band e v m px py -
    a ^ 2 * currentBandBlockTrace ν μ (oppositeBand band) band e v m px py

/-- At the target-band pole, the regular direction-indexed spectator/current factor converges to the
inverse squared interband gap multiplying the canonical antisymmetric current block. -/
theorem tendsto_interbandSpectatorCurrentFactor_at_bandPole
    (μ ν : Fin 2) (band : TwoBand) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        interbandSpectatorCurrentFactor μ ν
          band e v m px py (bandEnergy band v m px py) broadening)
      (nhds 0)
      (nhds
        (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2 *
          bastinInterbandBlockDifference μ ν band e v m px py)) := by
  have hret : Tendsto
      (fun broadening : ℝ =>
        scalarResolventCoefficient
          (retardedSpectralParameter (bandEnergy band v m px py) broadening)
          (bandEnergy (oppositeBand band) v m px py) ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
    simpa only [retardedSpectralParameter] using
      tendsto_oppositeBandCoefficient_sq_at_bandPole .retarded band v m px py hE
  have hadv : Tendsto
      (fun broadening : ℝ =>
        scalarResolventCoefficient
          (advancedSpectralParameter (bandEnergy band v m px py) broadening)
          (bandEnergy (oppositeBand band) v m px py) ^ 2)
      (nhds 0)
      (nhds (((((interbandEnergyGap band v m px py : ℝ) : ℂ))⁻¹) ^ 2)) := by
    simpa only [advancedSpectralParameter] using
      tendsto_oppositeBandCoefficient_sq_at_bandPole .advanced band v m px py hE
  have hμν := hret.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => currentBandBlockTrace μ ν (oppositeBand band) band e v m px py)
      (nhds 0)
      (nhds (currentBandBlockTrace μ ν (oppositeBand band) band e v m px py)))
  have hνμ := hadv.mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => currentBandBlockTrace ν μ (oppositeBand band) band e v m px py)
      (nhds 0)
      (nhds (currentBandBlockTrace ν μ (oppositeBand band) band e v m px py)))
  simpa [interbandSpectatorCurrentFactor, bastinInterbandBlockDifference, mul_sub] using
    hμν.sub hνμ

end

end QuantumTheory.Models.MassiveDirac
