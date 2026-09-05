import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleExtraction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-window interband Bastin-pair extraction in the massive Dirac model

The opposite-source interband Bastin pair factors exactly into `-2 i`, the target-band Lorentzian
spectral kernel, and the regular spectator/current factor.  The previous pole-extraction theorem
therefore lifts immediately to the actual interband Bastin pair integrated over the same fixed
target-centered energy window.

The result remains pointwise in momentum.  No momentum integration or momentum-limit interchange is
performed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Fixed target-centered energy-window integral of the interband Bastin pair whose source is the
opposite band and whose target is `band`. -/
noncomputable def targetCenteredInterbandBastinPairIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution (oppositeBand band) band e v m px py
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
    bastinBandPairContribution (oppositeBand band) band e v m px py
        (bandEnergy band v m px py + offset) broadening =
      (-2 * Complex.I) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            band e v m px py (offset, broadening))
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    band e v m px py (bandEnergy band v m px py + offset) broadening hbroadening]
  unfold targetCenteredInterbandSpectatorCurrentFactor
  rw [show bandEnergy band v m px py + offset - bandEnergy band v m px py = offset by ring]
  ring

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
  have hpole :=
    tendsto_targetCenteredInterbandSpectatorCurrentPoleIntegral
      band e v m px py radius hE hradiusPos hradius
  have hconst : Tendsto
      (fun _ : ℝ => (-2 * Complex.I : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * Complex.I)) := tendsto_const_nhds
  refine (hconst.mul hpole).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact (targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    band e v m px py radius broadening hbroadening.ne').symm

end

end AnomalousHall.MassiveDirac
