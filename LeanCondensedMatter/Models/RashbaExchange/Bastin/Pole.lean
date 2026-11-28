import LeanCondensedMatter.Models.RashbaExchange.Bastin.Bands
import LeanCondensedMatter.QuantumTheory.TwoBand
import LeanCondensedMatter.Transport.Streda.InterbandPole
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Rashba-exchange isolated interband Bastin pole and Berry curvature

For a selected target band, keep only its opposite-source Bastin band pair.
The target resolvent difference provides the Lorentzian pole, while the
opposite-source resolvent squares and ordered charge-current blocks form
the regular spectator. The generic interband-pole theorem controls the
fixed target-centered energy window and positive-broadening limit.

This proves a pointwise-in-momentum *isolated pair* limit, not a limit of
the complete Bastin response. The trace-cyclicity and Berry-current-block
identities are upstream in `Current` and `Bastin/Berry`, respectively.
No diagonal/spectator limit cancellation, occupation integration, momentum
integration, or limit interchange is claimed.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport QuantumTheory.TwoBand
open ContinuousLinearMap
open Filter

/-- Isolated opposite-source Bastin pair integrated over a fixed,
target-centered energy window. This is not the full Hall response. -/
noncomputable def targetCenteredInterbandBastinPairIntegral
    (params : Parameters) (band : TwoBand)
    (px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution params 0 1 (oppositeBand band) band
      px py (bandEnergy params band px py + offset) broadening

/-- The concrete isolated Rashba pair is the generic regularized
interband Bastin pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
    (params : Parameters) (band : TwoBand)
    (px py radius broadening : ℝ) (hbroadening : broadening ≠ 0) :
    targetCenteredInterbandBastinPairIntegral params band px py radius broadening =
      interbandBastinPoleIntegral
        (interbandEnergyGap params band px py)
        (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
        (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
        radius broadening := by
  unfold targetCenteredInterbandBastinPairIntegral interbandBastinPoleIntegral
    interbandPoleRegularFactorIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro offset _
  dsimp only
  simpa only [bastinBandPairContribution, interbandEnergyGap, mul_assoc] using
    (scalarBastinBandPairContribution_targetCentered
      (bandEnergy params (oppositeBand band) px py) (bandEnergy params band px py)
      offset broadening (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
      (currentBandBlockTrace params 1 0 (oppositeBand band) band px py) hbroadening)

/-- The regular target-pole coefficient gives precisely the Berry weight. -/
theorem interbandPoleRegularFactor_zero_im_eq_neg_chargeSq_berryCurvature
    (params : Parameters) (band : TwoBand) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    (interbandPoleRegularFactor
      (interbandEnergyGap params band px py)
      (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
      (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
      (0, 0)).im =
      -(params.signedCharge ^ 2 * berryCurvature params band px py) := by
  rw [interbandPoleRegularFactor_zero]
  rw [mul_comm, inv_pow, ← div_eq_mul_inv, ← Complex.ofReal_pow, Complex.div_ofReal_im]
  exact interbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    params band px py hE

/-- Pointwise clean fixed-window limit of the *isolated* opposite-source
Bastin pair. This is `-2π q² Ω_band(p)`; no full-response limit is asserted. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
    (params : Parameters) (band : TwoBand) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          params band px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-2 * Real.pi *
          (params.signedCharge ^ 2 * berryCurvature params band px py))) := by
  apply tendsto_interbandBastinPoleIntegral_re_of_eq_on_pos
    (interbandEnergyGap params band px py)
    (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
    (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
    radius (params.signedCharge ^ 2 * berryCurvature params band px py)
    (fun broadening => targetCenteredInterbandBastinPairIntegral
      params band px py radius broadening) hradiusPos hradius
  · intro broadening hbroadening
    exact targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
      params band px py radius broadening hbroadening.ne'
  · exact interbandPoleRegularFactor_zero_im_eq_neg_chargeSq_berryCurvature
      params band px py hE

/-- The clean local density extracted from one isolated opposite-source
Bastin pole. This is a single unweighted ordered-pair coefficient, not a
conductivity: it has no occupation factor, sum over bands, Hall factor `1/2`,
response prefactor, or momentum integral. -/
noncomputable def cleanLocalIsolatedBastinLimitDensity
    (params : Parameters) (band : TwoBand) (px py : ℝ) : ℝ :=
  -2 * Real.pi * (params.signedCharge ^ 2 * berryCurvature params band px py)

/-- The named isolated-pole density is attained on a fixed window narrower
than the interband energy separation as broadening approaches zero from above. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLocalDensity
    (params : Parameters) (band : TwoBand) (px py radius : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hradiusPos : 0 < radius)
    (hradius : radius < |interbandEnergyGap params band px py|) :
    Tendsto
      (fun broadening : ℝ =>
        (targetCenteredInterbandBastinPairIntegral
          params band px py radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cleanLocalIsolatedBastinLimitDensity params band px py)) := by
  simpa only [cleanLocalIsolatedBastinLimitDensity] using
    (tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
      params band px py radius hE hradiusPos hradius)

end

end QuantumTheory.Models.RashbaExchange
