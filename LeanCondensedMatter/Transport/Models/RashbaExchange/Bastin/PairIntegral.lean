import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleExtraction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-window Rashba-exchange interband Bastin-pair extraction

The opposite-source interband Hall pair factors into `-2 i`, the target-band Lorentzian kernel,
and the regular spectator/current factor.  The generic pole-extraction result therefore lifts to
the actual Bastin pair at fixed momentum.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open Filter QuantumTheory.Transport

noncomputable def targetCenteredInterbandBastinPairIntegral
    (params : Parameters) (band : Band) (px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution params 0 1 (oppositeBand band) band
      px py (bandEnergy params band px py + offset) broadening

theorem targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
    (params : Parameters) (band : Band) (px py radius broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral
        params band px py radius broadening =
      (-2 * Complex.I) *
        targetCenteredInterbandSpectatorCurrentPoleIntegral
          params band px py radius broadening := by
  unfold targetCenteredInterbandBastinPairIntegral
    targetCenteredInterbandSpectatorCurrentPoleIntegral
    QuantumTheory.Transport.lorentzianRegularFactorIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro offset _
  change
    bastinBandPairContribution params 0 1 (oppositeBand band) band
        px py (bandEnergy params band px py + offset) broadening =
      (-2 * Complex.I) *
        ((lorentzianSpectralKernel offset broadening : ℂ) *
          targetCenteredInterbandSpectatorCurrentFactor
            params band px py (offset, broadening))
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    params 0 1 band px py
    (bandEnergy params band px py + offset) broadening hbroadening]
  unfold targetCenteredInterbandSpectatorCurrentFactor
  rw [show bandEnergy params band px py + offset -
      bandEnergy params band px py = offset by ring]
  ring

theorem tendsto_targetCenteredInterbandBastinPairIntegral
    (params : Parameters) (band : Band) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        targetCenteredInterbandBastinPairIntegral
          params band px py radius broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((-2 * Complex.I) *
          (Real.pi •
            targetCenteredInterbandSpectatorCurrentFactor
              params band px py (0, 0)))) := by
  have hpole :=
    tendsto_targetCenteredInterbandSpectatorCurrentPoleIntegral
      params band px py radius hE hradiusPos hradius
  have hconst : Tendsto
      (fun _ : ℝ => (-2 * Complex.I : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * Complex.I)) := tendsto_const_nhds
  refine (hconst.mul hpole).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact
    (targetCenteredInterbandBastinPairIntegral_eq_neg_two_i_mul_poleIntegral
      params band px py radius broadening hbroadening.ne').symm

end

end QuantumTheory.Transport.Models.RashbaExchange
