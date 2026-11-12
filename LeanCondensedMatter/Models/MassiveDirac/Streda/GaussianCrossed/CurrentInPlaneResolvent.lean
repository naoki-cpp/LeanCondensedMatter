import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientSourceY
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialHarmonics
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# In-plane Gaussian-crossed current: scalar Green difference and K2 remainder

For the *physical* source/Pauli in-plane crossed-current coefficients,
the transverse Pauli channel and the sum of the diagonal Pauli channels
have only the zeroth Fourier harmonic. Their RA two-propagator kernels
are therefore exact multiples of F_R(r) - F_A(r), after multiplication
by the physical spectral gap.

The traceless diagonal combination has an independent second-harmonic
K2 kernel, already evaluated to a resolvent-difference moment in
`RadialHarmonics`. It remains as a *specific nonzero-regulator residual*,
not an assumed vanishing term. Together with `CurrentGradientSourceY`,
this accounts for every radial-axis scalar/Pauli current component
without postulating the full Ado Eq. (14) identity.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- The difference of the *actual* two finite-cutoff R/A scalar
Green generators is the physical, first-free K0 Fourier resolvent
difference. The interval integral is finite and its subtraction uses
proved continuity (rather than an improper-integral manipulation). -/
private theorem gaussianCrossed_GreenGenerator_sub_eq_K0_integral
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        .retarded v m probeEnergy broadening disorderStrength hbar pMax radius -
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        .advanced v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
            ((finiteCutoffContinuumBornDysonDenominator
              .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
             (finiteCutoffContinuumBornDysonDenominator
              .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
  let oneSide : SpectralSide → ℝ → ℂ := fun side p =>
    (p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
      polarFourierZerothAngularKernel (p * radius / hbar)
  have hcont (side : SpectralSide) : Continuous (oneSide side) := by
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
        polarFourierZerothAngularKernel (p * radius / hbar)) :=
      continuous_polarFourierZerothAngularKernel.comp (by fun_prop)
    change Continuous (fun p : ℝ =>
      ((p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
        polarFourierZerothAngularKernel (p * radius / hbar))
    exact (Complex.continuous_ofReal.mul (hdenCont.inv₀ hden)).mul hK
  have hRint : IntervalIntegrable (oneSide .retarded) volume 0 pMax :=
    (hcont .retarded).intervalIntegrable 0 pMax
  have hAint : IntervalIntegrable (oneSide .advanced) volume 0 pMax :=
    (hcont .advanced).intervalIntegrable 0 pMax
  unfold finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ((∫ p in (0 : ℝ)..pMax, oneSide .retarded p) -
         (∫ p in (0 : ℝ)..pMax, oneSide .advanced p)) := by
      dsimp [oneSide]
      ring
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          oneSide .retarded p - oneSide .advanced p := by
      rw [intervalIntegral.integral_sub hRint hAint]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro p _
      dsimp [oneSide]
      ring

/-- General K0 spectral-gap bridge. This reduces an *actual finite*
current integral to the physical scalar Green difference, assuming
the pointwise kernel is a fixed spectral coefficient times the
R/A single-resolvent difference. -/
private theorem gaussianCrossed_K0_current_gap_eq_Green_difference
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax)
    (coeff : ℂ) (kernel : ℝ → ℂ)
    (hpoint : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax * kernel p =
        coeff * ((p : ℂ) *
          polarFourierZerothAngularKernel (p * radius / hbar) *
          ((finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
           (finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹))) :
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax, kernel p) =
      coeff *
        (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax radius) := by
  rw [gaussianCrossed_GreenGenerator_sub_eq_K0_integral
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRASpectralGap
            v m probeEnergy broadening disorderStrength hbar pMax * kernel p := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          coeff * ((p : ℂ) *
            polarFourierZerothAngularKernel (p * radius / hbar) *
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

/-- Exact physical in-plane *transverse* crossed-current coefficient:
the off-diagonal K0 term is the Green R/A difference, with the
energy-mass antisymmetric coefficient and correct Pauli phase. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedInPlaneTransverse_gap_eq_Green_difference
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .x 1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (-Complex.I * (eR * mA - eA * mR) * factor) *
        (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax radius) := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
    .x 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  apply gaussianCrossed_K0_current_gap_eq_Green_difference
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
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

/-- Physical diagonal source-x and source-y Pauli trace: the K0
part of the full current is an *exact* Green-generator difference.
The traceless diagonal K2 harmonic is independent and is not silently
dropped as an assumed vanishing residual. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedInPlaneTrace_gap_eq_Green_difference
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax * (jxx + jyy) =
      (2 * (eA * eR - mA * mR) * factor) *
        (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          .advanced v m probeEnergy broadening disorderStrength hbar pMax radius) := by
  dsimp only
  let factor : ℂ := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let advanced : ℝ → FiniteCutoffBornDysonRadialPauliData := fun p =>
    finiteCutoffContinuumBornDysonRadialPauliData
      .advanced v m p probeEnergy broadening disorderStrength hbar pMax
  let retarded : ℝ → FiniteCutoffBornDysonRadialPauliData := fun p =>
    finiteCutoffContinuumBornDysonRadialPauliData
      .retarded v m p probeEnergy broadening disorderStrength hbar pMax
  have hdiag := (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax).1
  dsimp only at hdiag
  rw [hdiag]
  apply gaussianCrossed_K0_current_gap_eq_Green_difference
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  intro p
  have hgap := finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    v m probeEnergy broadening disorderStrength hbar pMax p
    hbroadening hdisorder hpMax
  dsimp [factor, advanced, retarded, finiteCutoffContinuumBornDysonRadialPauliData,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]
  rw [← hgap]
  ring

end

end QuantumTheory.Models.MassiveDirac
