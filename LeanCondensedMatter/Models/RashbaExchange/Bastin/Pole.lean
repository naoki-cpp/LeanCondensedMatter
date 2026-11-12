import LeanCondensedMatter.Models.RashbaExchange.Bastin.Bands
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

open QuantumTheory.Transport
open ContinuousLinearMap
open Filter

/-- The source-band scalar coefficient at energy `E_target + offset` is
the generic target-centered source resolvent, with the full Rashba band
energies and their common kinetic shift cancelling only in the gap. -/
theorem sourceCoefficient_targetCentered
    (side : SpectralSide) (params : Parameters) (band : Band)
    (px py offset broadening : ℝ) :
    scalarResolventCoefficient
        (spectralParameter side (bandEnergy params band px py + offset) broadening)
        (bandEnergy params (oppositeBand band) px py) =
      targetCenteredSourceCoefficient side
        (interbandEnergyGap params band px py) offset broadening := by
  unfold targetCenteredSourceCoefficient scalarResolventCoefficient
    spectralParameter spectralParameterOfRegulator interbandEnergyGap
  congr 1
  push_cast
  ring

/-- At nonzero broadening the opposite-source contribution factorizes
exactly into the target-band Lorentzian and the generic regular spectator. -/
theorem bastinBandPairContribution_opposite_source_eq_lorentzian
    (params : Parameters) (μ ν : Fin 2) (band : Band)
    (px py offset broadening : ℝ) (hbroadening : broadening ≠ 0) :
    bastinBandPairContribution params μ ν (oppositeBand band) band
        px py (bandEnergy params band px py + offset) broadening =
      (-2 * Complex.I) *
        (Lorentzian.spectralKernel offset broadening : ℂ) *
        interbandPoleRegularFactor
          (interbandEnergyGap params band px py)
          (currentBandBlockTrace params μ ν (oppositeBand band) band px py)
          (currentBandBlockTrace params ν μ (oppositeBand band) band px py)
          (offset, broadening) := by
  unfold bastinBandPairContribution interbandPoleRegularFactor
  dsimp
  rw [scalarSpectralDifferenceCoefficient_eq_lorentzian
      (bandEnergy params band px py)
      (bandEnergy params band px py + offset) broadening hbroadening]
  simp only [retardedSpectralParameter, advancedSpectralParameter]
  rw [sourceCoefficient_targetCentered .retarded params band px py offset broadening,
    sourceCoefficient_targetCentered .advanced params band px py offset broadening]
  rw [show bandEnergy params band px py + offset -
      bandEnergy params band px py = offset by ring]
  ring

/-- Isolated opposite-source Bastin pair integrated over a fixed,
target-centered energy window. This is not the full Hall response. -/
noncomputable def targetCenteredInterbandBastinPairIntegral
    (params : Parameters) (band : Band)
    (px py radius broadening : ℝ) : ℂ :=
  ∫ offset in -radius..radius,
    bastinBandPairContribution params 0 1 (oppositeBand band) band
      px py (bandEnergy params band px py + offset) broadening

/-- The concrete isolated Rashba pair is the generic regularized
interband Bastin pole integral. -/
theorem targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
    (params : Parameters) (band : Band)
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
  rw [bastinBandPairContribution_opposite_source_eq_lorentzian
    params 0 1 band px py offset broadening hbroadening]
  ring

/-- The regular target-pole coefficient gives precisely the Berry weight. -/
theorem interbandPoleRegularFactor_zero_im_eq_neg_chargeSq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    (interbandPoleRegularFactor
      (interbandEnergyGap params band px py)
      (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
      (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
      (0, 0)).im =
      -(params.signedCharge ^ 2 * berryCurvature params band px py) := by
  rw [interbandPoleRegularFactor_zero]
  have hgap : interbandEnergyGap params band px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero params band px py hE
  have hcoeff :
      (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2) =
        ((((interbandEnergyGap params band px py)⁻¹ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  calc
    (((((interbandEnergyGap params band px py : ℝ) : ℂ))⁻¹) ^ 2 *
      (currentBandBlockTrace params 0 1 (oppositeBand band) band px py -
        currentBandBlockTrace params 1 0 (oppositeBand band) band px py)).im =
      (currentBandBlockTrace params 0 1 (oppositeBand band) band px py -
        currentBandBlockTrace params 1 0 (oppositeBand band) band px py).im /
        interbandEnergyGap params band px py ^ 2 := by
      rw [hcoeff]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
      field_simp [hgap]
      ring
    _ = -(params.signedCharge ^ 2 * berryCurvature params band px py) :=
      interbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
        params band px py hE

/-- Pointwise clean fixed-window limit of the *isolated* opposite-source
Bastin pair. This is `-2π q² Ω_band(p)`; no full-response limit is asserted. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_berryCurvature
    (params : Parameters) (band : Band) (px py radius : ℝ)
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
  have hgeneric :=
    tendsto_interbandBastinPoleIntegral_re
      (interbandEnergyGap params band px py)
      (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
      (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
      radius hradiusPos hradius
  have him :=
    interbandPoleRegularFactor_zero_im_eq_neg_chargeSq_berryCurvature
      params band px py hE
  have hgeneric' : Tendsto
      (fun broadening : ℝ =>
        (interbandBastinPoleIntegral
          (interbandEnergyGap params band px py)
          (currentBandBlockTrace params 0 1 (oppositeBand band) band px py)
          (currentBandBlockTrace params 1 0 (oppositeBand band) band px py)
          radius broadening).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (-2 * Real.pi *
          (params.signedCharge ^ 2 * berryCurvature params band px py))) := by
    simpa [him] using hgeneric
  refine hgeneric'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
  exact congrArg Complex.re
    (targetCenteredInterbandBastinPairIntegral_eq_interbandBastinPoleIntegral
      params band px py radius broadening hbroadening.ne').symm

/-- The clean local density extracted from one isolated opposite-source
Bastin pole. This is a single unweighted ordered-pair coefficient, not a
conductivity: it has no occupation factor, sum over bands, Hall factor `1/2`,
response prefactor, or momentum integral. -/
noncomputable def cleanLocalIsolatedBastinLimitDensity
    (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  -2 * Real.pi * (params.signedCharge ^ 2 * berryCurvature params band px py)

/-- The named isolated-pole density is attained on a fixed window narrower
than the interband energy separation as broadening approaches zero from above. -/
theorem tendsto_targetCenteredInterbandBastinPairIntegral_re_cleanLocalDensity
    (params : Parameters) (band : Band) (px py radius : ℝ)
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
