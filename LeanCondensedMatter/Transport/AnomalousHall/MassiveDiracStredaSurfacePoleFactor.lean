import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinPoleFactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Massive-Dirac Středa surface pole factor

The zero-temperature Středa surface primitive has already been decomposed into ordered band
blocks.  This file isolates the interband block whose target band carries the Fermi-shell pole.
Exactly as in the Bastin pole analysis, the singular target-band retarded-minus-advanced factor is
a Lorentzian while the opposite-band resolvent is a regular spectator.

The Středa surface primitive contains one spectator resolvent rather than the squared spectator in
the Bastin kernel.  We therefore name that regular factor separately and record its target-pole
limit.  No momentum integration or broadening-limit interchange is performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Regular opposite-band spectator/current factor multiplying the target-band Lorentzian in one
interband Středa surface block. -/
noncomputable def stredaSurfaceSpectatorCurrentFactor
    (band : Band) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening)
    (oppositeBand band) v m px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening)
    (oppositeBand band) v m px py
  r * bastinXYBandBlockTrace (oppositeBand band) band e v m px py -
    a * bastinYXBandBlockTrace (oppositeBand band) band e v m px py

/-- Exact factorization of the opposite-source interband Středa surface block into the target-band
Lorentzian and a regular spectator/current factor. -/
theorem stredaSurfaceBandPairContribution_opposite_source_eq_lorentzian
    (band : Band) (e v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    stredaSurfaceBandPairContribution (oppositeBand band) band
        e v m px py probeEnergy broadening =
      Complex.I *
        (lorentzianSpectralKernel
          (probeEnergy - bandEnergy band v m px py) broadening : ℂ) *
        stredaSurfaceSpectatorCurrentFactor
          band e v m px py probeEnergy broadening := by
  unfold stredaSurfaceBandPairContribution stredaSurfaceSpectatorCurrentFactor
  dsimp
  rw [spectralDifferenceCoefficient_eq_lorentzian
    band v m px py probeEnergy broadening hbroadening]
  ring

/-- Target-centered form of the regular Středa surface spectator/current factor. -/
noncomputable def targetCenteredStredaSurfaceSpectatorCurrentFactor
    (band : Band) (e v m px py : ℝ) (z : ℝ × ℝ) : ℂ :=
  stredaSurfaceSpectatorCurrentFactor
    band e v m px py (bandEnergy band v m px py + z.1) z.2

/-- In target-centered coordinates the interband Středa surface block is a Lorentzian in the energy
offset times the regular surface spectator. -/
theorem stredaSurfaceBandPairContribution_opposite_source_targetCentered
    (band : Band) (e v m px py offset broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    stredaSurfaceBandPairContribution (oppositeBand band) band
        e v m px py (bandEnergy band v m px py + offset) broadening =
      Complex.I * (lorentzianSpectralKernel offset broadening : ℂ) *
        targetCenteredStredaSurfaceSpectatorCurrentFactor
          band e v m px py (offset, broadening) := by
  rw [stredaSurfaceBandPairContribution_opposite_source_eq_lorentzian
    band e v m px py (bandEnergy band v m px py + offset) broadening hbroadening]
  unfold targetCenteredStredaSurfaceSpectatorCurrentFactor
    stredaSurfaceSpectatorCurrentFactor
  rw [show bandEnergy band v m px py + offset - bandEnergy band v m px py = offset by ring]

/-- The opposite-band surface spectator is regular at the target-band pole.  Its clean pole value
is the inverse interband gap multiplying the antisymmetric current block. -/
theorem tendsto_stredaSurfaceSpectatorCurrentFactor_at_bandPole
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        stredaSurfaceSpectatorCurrentFactor
          band e v m px py (bandEnergy band v m px py) broadening)
      (nhds 0)
      (nhds
        (((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
            bastinXYBandBlockTrace (oppositeBand band) band e v m px py -
          ((interbandEnergyGap band v m px py : ℝ) : ℂ)⁻¹ *
            bastinYXBandBlockTrace (oppositeBand band) band e v m px py)) := by
  have hret := tendsto_retarded_oppositeBandCoefficient_at_bandPole
    band v m px py hE
  have hadv := tendsto_advanced_oppositeBandCoefficient_at_bandPole
    band v m px py hE
  have hxy := hret.mul
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℝ => bastinXYBandBlockTrace (oppositeBand band) band e v m px py)
        (nhds 0)
        (nhds (bastinXYBandBlockTrace (oppositeBand band) band e v m px py)))
  have hyx := hadv.mul
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℝ => bastinYXBandBlockTrace (oppositeBand band) band e v m px py)
        (nhds 0)
        (nhds (bastinYXBandBlockTrace (oppositeBand band) band e v m px py)))
  simpa [stredaSurfaceSpectatorCurrentFactor] using hxy.sub hyx

end

end AnomalousHall.MassiveDirac
