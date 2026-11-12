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
the complete Bastin response. No diagonal/spectator limit cancellation,
occupation integration, momentum integration, or limit interchange is claimed.
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

/-- Cyclicity of finite-dimensional trace exchanges the current directions
and swaps the ordered band projectors, without complex conjugation. -/
theorem currentBandBlockTrace_swap
    (params : Parameters) (μ ν : Fin 2) (source target : Band)
    (px py : ℝ) :
    currentBandBlockTrace params ν μ source target px py =
      currentBandBlockTrace params μ ν target source px py := by
  unfold currentBandBlockTrace
  simpa only [mul_assoc] using
    (finiteDimensionalOperatorTrace_mul_comm
      (bandProjectorOperator params target px py *
        currentBoundedOperator params ν px py)
      (bandProjectorOperator params source px py *
        currentBoundedOperator params μ px py))

/-- The antisymmetric imaginary current block for a target band, normalized
by its squared interband gap, is minus signed-charge-squared Berry curvature. -/
theorem interbandBlockDifference_im_div_gap_sq_eq_neg_chargeSq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    (currentBandBlockTrace params 0 1 (oppositeBand band) band px py -
      currentBandBlockTrace params 1 0 (oppositeBand band) band px py).im /
        interbandEnergyGap params band px py ^ 2 =
      -(params.signedCharge ^ 2 * berryCurvature params band px py) := by
  have hband :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      params band px py hE
  have hopp :=
    two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
      params (oppositeBand band) px py hE
  simp only [oppositeBand_oppositeBand, interbandEnergyGap_oppositeBand,
    berryCurvature_oppositeBand, neg_sq] at hopp
  rw [currentBandBlockTrace_swap params 0 1 (oppositeBand band) band]
  rw [Complex.sub_im]
  have hgap : interbandEnergyGap params band px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_spinOrbitEnergy_ne_zero params band px py hE
  field_simp [hgap] at hband hopp ⊢
  nlinarith

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

end

end QuantumTheory.Models.RashbaExchange
