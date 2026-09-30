import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleExtraction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-window interband Bastin-pair extraction in the massive Dirac model

The model-specific ordered band pair is identified with the generic isolated interband Bastin pole.
The fixed-window zero-broadening limit is then inherited from
`Transport.Streda.InterbandPole`.

The result remains pointwise in momentum. No momentum integration or momentum-limit interchange is
performed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Fixed target-centered energy-window integral of the interband Bastin Hall pair whose source is
the opposite band and whose target is `band`. -/
noncomputable def targetCenteredInterbandBastinPairIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution 0 1 (oppositeBand band) band e v m px py
      (bandEnergy band v m px py + offset) broadening

/-- For nonzero broadening, the integrated opposite-source Bastin pair is exactly `-2 i` times the
regular-factor pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    (band : Band) (e v m px py radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral
        band e v m px py radius broadening =
      (-2 * Complex.I) *
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          band e v m px py radius broadening := by
  unfold targetCenteredInterbandBastinPairIntegral
    targetCenteredInterbandSpectatorCurrentPoleIntegral
    QuantumTheory.Transport.lorentzianRegularFactorIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro offset _
  change
    bastinBandPairContribution 0 1 (oppositeBand band) band e v m px py
        (bandEnergy band v m px py + offset) broadening =
      (-2 * Complex.I) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (offset, broadening))
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    0 1 band e v m px py (bandEnergy band v m px py + offset) broadening hbroadening]
  unfold targetCenteredInterbandSpectatorCurrentFactor
  rw [show bandEnergy band v m px py + offset - bandEnergy band v m px py = offset by ring]
  ring

/-- At nonzero broadening, the concrete massive-Dirac pair integral is the generic isolated
interband Bastin pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral
        band e v m px py radius broadening =
      interbandBastinPoleIntegral
        (interbandEnergyGap band v m px py)
        (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
        (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
        radius broadening := by
  rw [targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    band e v m px py radius broadening hbroadening]
  unfold interbandBastinPoleIntegral
  rw [targetCenteredInterbandSpectatorCurrentPoleIntegral_eq_interbandPoleRegularFactorIntegral]

/-- On a fixed positive target-centered window narrower than the interband gap, the integrated
opposite-source Bastin pair converges to `-2 i π` times the regular factor at the target pole. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral
    (band : Band) (e v m px py radius : ℝ)
    (hE : energy v m px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap band v m px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandBastinPairIntegral
          band e v m px py radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((-2 * Complex.I) *
          (Real.pi •
            targetCenteredInterbandSpectatorCurrentFactor
              band e v m px py (0, 0)))) := by
  have hgeneric :=
    tendsto_interbandBastinPoleIntegral
      (interbandEnergyGap band v m px py)
      (bastinBandBlockTrace 0 1 (oppositeBand band) band e v m px py)
      (bastinBandBlockTrace 1 0 (oppositeBand band) band e v m px py)
      radius hradiusPos hradius
  refine hgeneric.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact
    (targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
      band e v m px py radius broadening hbroadening.ne').symm

end

end QuantumTheory.Transport.Models.MassiveDirac
