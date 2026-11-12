import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientBridge
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarGenerator
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Actual crossed current as a derivative of the physical R/A Green generators

The source-x scalar and z-Pauli crossed-current components from
`CurrentGradientBridge` contain the *physical* single-resolvent
first-harmonic difference. The finite-cutoff Green generators
already have proved radial derivatives. This file identifies the
difference moment with the **difference of those derivatives**,
including the Fourier scale and exactly one physical momentum measure.

At finite external broadening and cutoff, for nonzero hbar:

  i M_RA(r) = hbar (F_R'(r) - F_A'(r)).

Consequently the actual source-x scalar/z crossed-current coefficients
obey exact **spectral-gap-multiplied** gradient identities. No division
by the spectral gap, weak-disorder asymptotics, running-cutoff removal,
or claim about the full matrix current is made here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- One causal Green-generator derivative equals its first-harmonic
moment after restoring the radial Fourier scale. This is a finite-cutoff
theorem and does not exchange a derivative with an improper integral. -/
private theorem finiteCutoffContinuumBornDysonScalarGenerator_scaled_deriv
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    (hbar : ℂ) *
      deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax r) radius =
      Complex.I * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          ((p : ℂ) ^ 2) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
  have hderiv :=
    (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt
      side v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax).deriv
  have hratio (p : ℝ) :
      (hbar : ℂ) * (((p / hbar : ℝ) : ℂ)) = (p : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hhbar]
  have hpoint (p : ℝ) :
      (hbar : ℂ) *
        (((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
          (Complex.I * (((p / hbar : ℝ) : ℂ)) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar))) =
      Complex.I * (((p : ℂ) ^ 2) *
        polarFourierFirstCosineAngularKernel (p * radius / hbar) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
    calc
      _ = ((hbar : ℂ) * (((p / hbar : ℝ) : ℂ))) *
          (Complex.I * ((p : ℂ) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)) := by ring
      _ = _ := by rw [hratio]; ring
  rw [hderiv]
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (hbar : ℂ) *
            (((p : ℂ) *
                (finiteCutoffContinuumBornDysonDenominator
                  side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
              (Complex.I * (((p / hbar : ℝ) : ℂ)) *
                polarFourierFirstCosineAngularKernel (p * radius / hbar))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          Complex.I * (((p : ℂ) ^ 2) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro p _
      exact hpoint p
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      ring

/-- The exact, physically normalized R/A first-harmonic difference is
the radial derivative of the **actual** retarded-minus-advanced scalar
Born-Dyson Green generators. The imaginary Fourier phase and hbar are
not discarded or absorbed into a new definition. -/
theorem finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment_eq_gradient
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    Complex.I * finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
      v m probeEnergy broadening disorderStrength hbar pMax radius =
      (hbar : ℂ) *
        (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
         deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius) := by
  let moment : SpectralSide → ℝ → ℂ := fun side p =>
    ((p : ℂ) ^ 2) *
      polarFourierFirstCosineAngularKernel (p * radius / hbar) *
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
  have hcont (side : SpectralSide) : Continuous (moment side) := by
    have hden (p : ℝ) :
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 :=
      finiteCutoffContinuumBornDysonDenominator_ne_zero
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax
    have hdenCont : Continuous (fun p : ℝ =>
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax) := by
      unfold finiteCutoffContinuumBornDysonDenominator
      fun_prop
    have hK : Continuous (fun p : ℝ =>
        polarFourierFirstCosineAngularKernel (p * radius / hbar)) :=
      continuous_polarFourierFirstCosineAngularKernel.comp (by fun_prop)
    change Continuous (fun p : ℝ =>
      ((p : ℂ) ^ 2 *
        polarFourierFirstCosineAngularKernel (p * radius / hbar)) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)
    exact ((Complex.continuous_ofReal.pow 2).mul hK).mul
      (hdenCont.inv₀ hden)
  have hRint : IntervalIntegrable (moment .retarded) volume 0 pMax :=
    (hcont .retarded).intervalIntegrable 0 pMax
  have hAint : IntervalIntegrable (moment .advanced) volume 0 pMax :=
    (hcont .advanced).intervalIntegrable 0 pMax
  have hmoment :
      finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
        v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ((∫ p in (0 : ℝ)..pMax, moment .retarded p) -
         (∫ p in (0 : ℝ)..pMax, moment .advanced p)) := by
    unfold finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
    calc
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax, moment .retarded p - moment .advanced p := by
          congr 1
          apply intervalIntegral.integral_congr
          intro p _
          dsimp [moment]
          ring
      _ = _ := by rw [intervalIntegral.integral_sub hRint hAint]
  have hR :=
    finiteCutoffContinuumBornDysonScalarGenerator_scaled_deriv
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      hhbar hbroadening hdisorder hpMax
  have hA :=
    finiteCutoffContinuumBornDysonScalarGenerator_scaled_deriv
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      hhbar hbroadening hdisorder hpMax
  calc
    Complex.I * finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
      v m probeEnergy broadening disorderStrength hbar pMax radius =
      Complex.I * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ((∫ p in (0 : ℝ)..pMax, moment .retarded p) -
         (∫ p in (0 : ℝ)..pMax, moment .advanced p)) := by rw [hmoment]
    _ = (hbar : ℂ) *
        deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
        (hbar : ℂ) *
        deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius := by
          rw [hR, hA]
          dsimp [moment]
          ring
    _ = _ := by ring

/-- The **integrated physical scalar** crossed-current coefficient is
an exact spectral-gap-multiplied gradient of the R/A Green generators.
The equality does not divide by the gap, hence makes no claim that
the leading-order Ado Eq. (14) current identity holds at all regulators. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_gap_gradient
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    Complex.I * (finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        0 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      ((v : ℂ) * (eR + eA) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax) *
      ((hbar : ℂ) *
        (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
         deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_gap_eq
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  rw [← finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment_eq_gradient
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax]
  ring

/-- The physical source-x Pauli-z crossed current obeys the same
finite-cutoff derivative bridge with the sum of effective R/A masses. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_gap_gradient
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    Complex.I * (finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      ((v : ℂ) * (mR + mA) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax) *
      ((hbar : ℂ) *
        (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
         deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_gap_eq
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  rw [← finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment_eq_gradient
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax]
  ring

end

end QuantumTheory.Models.MassiveDirac
