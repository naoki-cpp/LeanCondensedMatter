import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Boundary
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-cutoff zero-broadening boundary of finite-eta Born-Dyson data

This module starts from the common complex Born boundary and propagates it through the finite-`η`
Born-Dyson effective energy and mass and radial denominator. The external broadening limit is taken
at fixed disorder strength and fixed cutoff, retaining the finite real self-energy contribution
explicitly.

The same boundary owns the real Born renormalization and the denominator regularity it controls.
Under positive disorder, nonzero velocity and `ℏ`, the metallic condition, and renormalization below
one, every side-indexed zero-broadening denominator is nonzero; the retarded-advanced denominator
product is therefore nonzero as well.

No disorder-strength limit, ultraviolet removal, limit interchange, Hall projection, mechanism
label, SCBA/Ward claim, or exact-disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective energy. -/
def finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (probeEnergy : ℂ) -
    ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
      ((probeEnergy : ℂ) *
        finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax)

/-- Fixed-cutoff zero-broadening boundary of the finite-`η` Born-Dyson effective mass. -/
def finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  (m : ℂ) +
    ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
      ((m : ℂ) *
        finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax)

/-- The finite-`η` effective spectral energy converges to its full complex fixed-cutoff boundary. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hsigma :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .scalar side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hspectral :
      Tendsto
        (fun broadening : ℝ => spectralParameter side probeEnergy broadening)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (probeEnergy : ℂ)) := by
    have hcontinuous :
        ContinuousAt (fun broadening : ℝ => spectralParameter side probeEnergy broadening) 0 := by
      unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
      fun_prop
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
      hcontinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa [finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary,
    bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
    SpectralSide.regulator, spectralParameterOfRegulator] using
    hspectral.sub hsigma

/-- The finite-`η` effective Dirac mass converges to its full complex fixed-cutoff boundary. -/
theorem tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
          side v m probeEnergy disorderStrength hbar pMax)) := by
  have hsigma :=
    tendsto_finiteCutoffContinuumBornSelfEnergyCoefficient_broadening_zero
      .z side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hmass :
      Tendsto (fun _ : ℝ => (m : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (m : ℂ)) := tendsto_const_nhds
  simpa [finiteCutoffContinuumBornEffectiveMass,
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary,
    bornSelfEnergyChannelWeight, bornSelfEnergyChannelWeightOfRegulator,
    SpectralSide.regulator] using
    hmass.add hsigma

/-- Fixed-momentum zero-broadening boundary of the finite-cutoff Born-Dyson quadratic denominator. -/
def finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
      side v m probeEnergy disorderStrength hbar pMax ^ 2 -
    ((v ^ 2 * p ^ 2 : ℝ) : ℂ)

/-- At fixed radial momentum, the finite-`η` Born-Dyson denominator converges to its explicit
fixed-cutoff zero-broadening boundary at fixed disorder strength. -/
theorem tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          side v m p probeEnergy disorderStrength hbar pMax)) := by
  have henergy :=
    tendsto_finiteCutoffContinuumBornEffectiveEnergy_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hmass :=
    tendsto_finiteCutoffContinuumBornEffectiveMass_broadening_zero
      side v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary, pow_two] using
    ((henergy.mul henergy).sub (hmass.mul hmass)).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => ((v ^ 2 * p ^ 2 : ℝ) : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))

/-- Fixed-cutoff zero-broadening boundary of the radial retarded-advanced Born-Dyson denominator
product consumed by the Hall common-denominator form. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m p probeEnergy disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .advanced v m p probeEnergy disorderStrength hbar pMax

/-- The finite-`η` radial RA denominator product converges at fixed disorder strength to the product
of the separately established retarded and advanced zero-broadening boundaries. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_broadening_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
          v m p probeEnergy disorderStrength hbar pMax)) := by
  have hret := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    .retarded v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  have hadv := tendsto_finiteCutoffContinuumBornDysonDenominator_broadening_zero
    .advanced v m p probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct,
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary] using
    hret.mul hadv

/-- Dimensionless real finite-cutoff Born renormalization entering the zero-broadening effective
energy and mass. The real part is intentional here: this quantity tracks the real self-energy shift,
not a conversion from a complex observable to a real one. -/
def finiteCutoffContinuumBornBoundaryRealRenormalization
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
    (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      .retarded v m probeEnergy pMax).re

/-- The real Born renormalization is independent of the retarded/advanced side used to read the
real part of the common complex boundary value. -/
theorem finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side
    (side : SpectralSide)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).re =
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax := by
  cases side <;>
    simp [finiteCutoffContinuumBornBoundaryRealRenormalization,
      finiteCutoffContinuumBornDenominatorIntegralBoundaryValue,
      pauliGreenDenominator, SpectralSide.regulator]

private theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax).im =
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
        (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
          side v m probeEnergy pMax).im *
        (probeEnergy ^ 2 + m ^ 2 -
          (disorderStrength * continuumBornAngularMeasurePrefactor hbar) *
            (finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
              side v m probeEnergy pMax).re *
            (probeEnergy ^ 2 - m ^ 2)) := by
  unfold finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveEnergyZeroBroadeningBoundary
    finiteCutoffContinuumBornEffectiveMassZeroBroadeningBoundary
  simp only [pow_two, Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add]
  ring

private theorem continuumBornAngularMeasurePrefactor_pos
    (hbar : ℝ) (hhbar : hbar ≠ 0) :
    0 < continuumBornAngularMeasurePrefactor hbar := by
  unfold continuumBornAngularMeasurePrefactor momentumMeasurePrefactor
  have hden : 0 < (2 * Real.pi * hbar) ^ 2 :=
    sq_pos_of_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (one_div_pos.mpr hden)

/-- Positive disorder and a real-renormalization bound below one keep the side-indexed fixed-cutoff
zero-broadening Born-Dyson denominator away from zero at every radial momentum. -/
theorem finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
    (side : SpectralSide)
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      side v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hmetalSq : m ^ 2 < probeEnergy ^ 2 := by
    rw [← sq_abs m]
    nlinarith [abs_nonneg m]
  have hgap : 0 < probeEnergy ^ 2 - m ^ 2 := sub_pos.mpr hmetalSq
  have hmeasure : 0 < continuumBornAngularMeasurePrefactor hbar :=
    continuumBornAngularMeasurePrefactor_pos hbar hhbar
  have hg :
      0 < disorderStrength * continuumBornAngularMeasurePrefactor hbar :=
    mul_pos hdisorder hmeasure
  let J : ℂ :=
    finiteCutoffContinuumBornDenominatorIntegralBoundaryValue
      side v m probeEnergy pMax
  let lambda : ℝ :=
    (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.re
  have hlambda : lambda < 1 := by
    dsimp [lambda, J]
    rw [finiteCutoffContinuumBornBoundaryRealRenormalization_eq_side]
    exact hrenorm
  have hlambdaGap :
      lambda * (probeEnergy ^ 2 - m ^ 2) < probeEnergy ^ 2 - m ^ 2 := by
    simpa using mul_lt_mul_of_pos_right hlambda hgap
  have hbracket :
      0 < probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2) := by
    nlinarith [hlambdaGap, sq_nonneg m]
  have hJim : J.im ≠ 0 := by
    dsimp [J]
    rw [finiteCutoffContinuumBornDenominatorIntegralBoundaryValue_im]
    have hvSq : v ^ 2 ≠ 0 := pow_ne_zero 2 hvelocity
    have htwoVSq : (2 * v ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hvSq
    have hinv : ((2 * v ^ 2)⁻¹ : ℝ) ≠ 0 := inv_ne_zero htwoVSq
    have hsign : side.sign ≠ 0 := by
      cases side <;> simp [SpectralSide.sign]
    exact mul_ne_zero (neg_ne_zero.mpr hinv) (mul_ne_zero hsign Real.pi_ne_zero)
  have himNe :
      (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        side v m p probeEnergy disorderStrength hbar pMax).im ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_im_eq]
    change
      -2 * (disorderStrength * continuumBornAngularMeasurePrefactor hbar) * J.im *
        (probeEnergy ^ 2 + m ^ 2 - lambda * (probeEnergy ^ 2 - m ^ 2)) ≠ 0
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hg)) hJim)
      (ne_of_gt hbracket)
  intro hzero
  apply himNe
  simpa using congrArg Complex.im hzero

/-- Under the same propagator-boundary hypotheses, the retarded-advanced zero-broadening denominator
product is nonzero at every radial momentum. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary_ne_zero
    (v m p probeEnergy disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax ≠ 0 := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
  exact mul_ne_zero
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .retarded v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      .advanced v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm)

end

end QuantumTheory.Transport.Models.MassiveDirac
