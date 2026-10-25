import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born–Dyson radial moments

Model-specific finite-cutoff radial integration laws for Born–Dyson denominators.
The single-pole logarithmic primitive, arbitrary-weight retarded–advanced
double-pole difference, and its logarithmic specialization are independent of a
particular conductivity or crossed diagram. The retarded–advanced moments are
consumed by Gaussian-crossed current harmonics, while the longitudinal same-side
RR/AA remainder retains its separate response-specific integral.
All identities retain finite broadening and cutoff without taking regulator limits.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport

/-- The finite-cutoff Born-Dyson single-pole radial integral is exactly
a difference of principal complex logarithms whenever the real part of
its effective spectral center is positive. Finite-`η` invertibility
excludes all real momentum poles and supplies the required nonzero
imaginary part of that center; no additional log-branch assumption is made.
This is before broadening and disorder limits. -/
theorem finiteBroadeningBornDyson_singlePoleRadialIntegral_eq_log_of_center_re_pos
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax)
    (hcenterRe : 0 <
      (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2).re) :
    (∫ p in (0 : ℝ)..pMax,
      (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        (Complex.log (finiteCutoffContinuumBornDysonDenominator
          side v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
          Complex.log (finiteCutoffContinuumBornDysonDenominator
            side v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) := by
  let energy := finiteCutoffContinuumBornEffectiveEnergy
    side v m probeEnergy broadening disorderStrength hbar pMax
  let mass := finiteCutoffContinuumBornEffectiveMass
    side v m probeEnergy broadening disorderStrength hbar pMax
  have hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0 := by
    intro p
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have him : (energy ^ 2 - mass ^ 2).im ≠ 0 :=
    massiveDiracRadialDenominator_center_im_ne_zero_of_re_pos
      v energy mass hvelocity hcenterRe hden
  have hlog := integral_massiveDiracRadialDenominatorKernel_eq_log
    v pMax energy mass hvelocity him
  simpa only [massiveDiracRadialDenominatorKernel,
    ← finiteCutoffContinuumBornDysonDenominator_eq_radial] using hlog

/-- Every finite-cutoff radial moment of the Born-Dyson RA double pole
reduces, after multiplication by the momentum-independent spectral center gap,
to a single-retarded-minus-single-advanced moment. This holds for arbitrary
complex radial weights, including all Gaussian-crossed Fourier harmonics.
No division by the center gap or broadening/cutoff limit is used. -/
theorem finiteCutoffContinuumBornDysonRadial_ra_weighted_moment_mul_center_gap
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) (weight : ℝ → ℂ) :
    let energyR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let energyA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let massR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let massA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
        (∫ p in (0 : ℝ)..pMax, weight p *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) =
      ∫ p in (0 : ℝ)..pMax, weight p *
        ((finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
         (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
  let energyR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let energyA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let massR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let massA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  have hgap (p : ℝ) :
      (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ =
        (finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
        (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
    have hnonzero (side : SpectralSide) :
        massiveDiracRadialDenominator v p
          (finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornEffectiveMass
            side v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0 := by
      rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
      exact finiteCutoffContinuumBornDysonDenominator_ne_zero
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax
    have hspectral :=
      massiveDiracRadialDenominator_inv_product_mul_center_gap
        v p energyR massR energyA massA (hnonzero .retarded) (hnonzero .advanced)
    dsimp only [energyR, energyA, massR, massA] at hspectral
    simpa only [massiveDiracRetardedAdvancedRadialDenominatorProduct,
      finiteCutoffContinuumBornDysonDenominator_eq_radial,
      ← finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul]
      using hspectral
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  dsimp only
  rw [← hgap p]
  ring

/-- At finite broadening and cutoff, the unweighted RA radial double-pole
moment reduces to logarithmic boundary values of the retarded and advanced
Dyson denominators. The spectral-center gap multiplies the moment, so the
identity does not silently assume that the gap is invertible. Positive real
parts of both spectral centers ensure the log-branch hypotheses by finite-η
Dyson invertibility. This is a radial building block, not an evaluation
of the nonzero-radius K0/K2 Fourier moments or an X/Psi conductivity. -/
theorem finiteCutoffContinuumBornDysonRadial_ra_pole_moment_mul_center_gap_eq_log
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax)
    (hcenterR : 0 <
      (finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2).re)
    (hcenterA : 0 <
      (finiteCutoffContinuumBornEffectiveEnergy
          .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2).re) :
    let energyR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let energyA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let massR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let massA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
        (∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) =
      -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) *
        ((Complex.log (finiteCutoffContinuumBornDysonDenominator
            .retarded v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
          Complex.log (finiteCutoffContinuumBornDysonDenominator
            .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) -
         (Complex.log (finiteCutoffContinuumBornDysonDenominator
            .advanced v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
          Complex.log (finiteCutoffContinuumBornDysonDenominator
            .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax))) := by
  have hmoment :=
    finiteCutoffContinuumBornDysonRadial_ra_weighted_moment_mul_center_gap
      v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax (fun p : ℝ => (p : ℂ))
  have hint (side : SpectralSide) : IntervalIntegrable
      (fun p : ℝ => (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)
      volume 0 pMax := by
    have hdenCont : Continuous
        (fun p : ℝ => finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax) := by
      unfold finiteCutoffContinuumBornDysonDenominator
      fun_prop
    have hdenNe (p : ℝ) :
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 :=
      finiteCutoffContinuumBornDysonDenominator_ne_zero
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax
    exact ((Complex.continuous_ofReal.comp continuous_id).mul
      (hdenCont.inv₀ hdenNe)).intervalIntegrable 0 pMax
  have hR := finiteBroadeningBornDyson_singlePoleRadialIntegral_eq_log_of_center_re_pos
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder hpMax hcenterR
  have hA := finiteBroadeningBornDyson_singlePoleRadialIntegral_eq_log_of_center_re_pos
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder hpMax hcenterA
  dsimp only at hmoment ⊢
  calc
    _ = ∫ p in (0 : ℝ)..pMax, (p : ℂ) *
        ((finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
         (finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) :=
      hmoment
    _ = (∫ p in (0 : ℝ)..pMax, (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) -
      (∫ p in (0 : ℝ)..pMax, (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
      rw [← intervalIntegral.integral_sub (hint .retarded) (hint .advanced)]
      apply intervalIntegral.integral_congr
      intro p _
      ring
    _ = _ := by
      rw [hR, hA]
      ring

end

end QuantumTheory.Models.MassiveDirac
