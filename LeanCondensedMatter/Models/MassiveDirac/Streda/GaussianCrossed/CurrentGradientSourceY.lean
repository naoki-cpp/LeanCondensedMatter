import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientDerivative
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Physical source-y crossed-current gradient bridge

The source-x scalar/z Gaussian-crossed current already has the exact
spectral-gap-multiplied gradient identity. The remaining *source-y* first
harmonics involve the advanced-minus-retarded effective mass and energy
rather than the corresponding sums. These identities connect both
source-y current channels directly to the same physical R/A Green
generator derivative.

All identities retain the finite Born reference cutoff, external
broadening, current-rung factor, momentum measure, and Fourier hbar.
No nonzero spectral-gap assumption or regulator limit is required.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- An integrated physical current K1 kernel with a pointwise RA
spectral-difference identity is an actual Green-generator gradient.
The prefactor is carried exactly once, rather than being assigned
independently to a reference Bessel integral. -/
private theorem gaussianCrossed_sourceY_gradient_of_kernel
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax)
    (coeff : ℂ) (kernel : ℝ → ℂ)
    (hpoint : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax * kernel p =
        coeff *
          (((p : ℂ) ^ 2) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((finiteCutoffContinuumBornDysonDenominator
              .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
             (finiteCutoffContinuumBornDysonDenominator
              .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹))) :
    Complex.I * (finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax *
      ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax, kernel p)) =
      coeff * ((hbar : ℂ) *
        (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
         deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) := by
  have hmoment :
      finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax *
        ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax, kernel p) =
      coeff * finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
        v m probeEnergy broadening disorderStrength hbar pMax radius := by
    unfold finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
    calc
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonRASpectralGap
              v m probeEnergy broadening disorderStrength hbar pMax * kernel p := by
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            coeff * (((p : ℂ) ^ 2) *
              polarFourierFirstCosineAngularKernel (p * radius / hbar) *
              ((finiteCutoffContinuumBornDysonDenominator
                .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
               (finiteCutoffContinuumBornDysonDenominator
                .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro p _
        exact hpoint p
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        ring
  rw [hmoment]
  rw [← finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment_eq_gradient
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax]
  ring

/-- Complete the physical first-harmonic scalar current bridge for
source-y. Unlike source-x, the coefficient is the *R/A mass difference*
and carries the Fourier/Pauli factor `-i`. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_sourceY_gap_gradient
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    Complex.I * (finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      (-Complex.I * ((v : ℂ) * (mA - mR) * factor)) *
        ((hbar : ℂ) *
          (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
           deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
    1 v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  apply gaussianCrossed_sourceY_gradient_of_kernel
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  intro p
  have hgap := finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    v m probeEnergy broadening disorderStrength hbar pMax p
    hbroadening hdisorder hpMax
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel,
    finiteCutoffContinuumBornDysonRadialPauliData,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]
  rw [← hgap]
  push_cast
  ring

/-- Complete the physical source-y Pauli-z crossed-current gradient:
its scalar coefficient is the *R/A effective-energy difference*.
The distinct source-y Pauli sign remains explicit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_sourceY_gap_gradient
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    Complex.I * (finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      (-Complex.I * ((v : ℂ) * (eA - eR) * factor)) *
        ((hbar : ℂ) *
          (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
           deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
    .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  apply gaussianCrossed_sourceY_gradient_of_kernel
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  intro p
  have hgap := finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    v m probeEnergy broadening disorderStrength hbar pMax p
    hbroadening hdisorder hpMax
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel,
    finiteCutoffContinuumBornDysonRadialPauliData,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]
  rw [← hgap]
  push_cast
  ring

end

end QuantumTheory.Models.MassiveDirac
