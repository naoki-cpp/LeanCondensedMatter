import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientSourceY
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialHarmonics
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.DysonShift
import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import LeanCondensedMatter.Analysis.Lorentzian.Pole
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.BornDyson.RegulatorBoundaryWeakDisorder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
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
open MeasureTheory Filter
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


/-- **Physical traceless K2 current = radial Green Hessian.**
At any finite momentum cutoff and nonzero external broadening, the
retarded/advanced spectral-gap-multiplied difference of the two
diagonal Gaussian-crossed current components is exactly the traceless
Hessian of the actual scalar Dyson Green generators. The radius is
multiplied rather than divided, so this also holds at the origin.

In particular, the anisotropic K2 current is *part* of the physical
matrix-gradient relation; it is not assumed to vanish or be subleading.
No disorder/broadening/UV/radius limit is taken. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedInPlaneK2_gap_eq_tracelessHessian
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let gap := finiteCutoffContinuumBornDysonRASpectralGap
      v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    let FR := fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .retarded v m probeEnergy broadening disorderStrength hbar pMax r
    let FA := fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .advanced v m probeEnergy broadening disorderStrength hbar pMax r
    (radius : ℂ) * gap * (jxx - jyy) =
      -2 * (v : ℂ) ^ 2 * factor * (hbar : ℂ) ^ 2 *
        ((radius : ℂ) * (deriv (deriv FR) radius - deriv (deriv FA) radius) -
          (deriv FR radius - deriv FA radius)) := by
  dsimp only
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let k2 : ℝ → ℂ := fun p =>
    polarFourierSecondCosineAngularKernel (p * radius / hbar)
  let invR : ℝ → ℂ := fun p =>
    (finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
  let invA : ℝ → ℂ := fun p =>
    (finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
  let momentR : ℝ → ℂ := fun p => (p : ℂ) ^ 3 * k2 p * invR p
  let momentA : ℝ → ℂ := fun p => (p : ℂ) ^ 3 * k2 p * invA p
  have hk2 := (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_spectral_difference
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax).2
  dsimp only [finiteCutoffContinuumBornDysonRASpectralGap] at hk2
  have hkernel (p : ℝ) :
      (2 * (p : ℂ) *
        (-(((2 * Real.pi : ℝ) : ℂ) *
          Complex.besselJ 2 ((p * radius / hbar : ℝ) : ℂ))) *
        ((((v * p : ℝ) : ℂ) ^ 2) * factor)) * (invR p - invA p) =
        (2 * (v : ℂ) ^ 2 * factor) *
          ((p : ℂ) ^ 3 * k2 p * (invR p - invA p)) := by
    dsimp [k2, factor]
    rw [polarFourierSecondCosineAngularKernel_eq_besselJ]
    push_cast
    ring
  have hk :
      finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax *
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
        2 * (v : ℂ) ^ 2 * factor * measure *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) ^ 3 * k2 p * (invR p - invA p) := by
    calc
      _ = measure * ∫ p in (0 : ℝ)..pMax,
            (2 * (v : ℂ) ^ 2 * factor) *
              ((p : ℂ) ^ 3 * k2 p * (invR p - invA p)) := by
            unfold finiteCutoffContinuumBornDysonRASpectralGap
            rw [hk2]
            congr 1
            apply intervalIntegral.integral_congr
            intro p _
            exact hkernel p
      _ = _ := by
            rw [intervalIntegral.integral_const_mul]
            ring
  have hcK2 : Continuous k2 :=
    continuous_polarFourierSecondCosineAngularKernel.comp (by fun_prop)
  have hcInvR : Continuous invR :=
    continuous_finiteCutoffContinuumBornDysonDenominator_inv_radial
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hcInvA : Continuous invA :=
    continuous_finiteCutoffContinuumBornDysonDenominator_inv_radial
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hcR : Continuous momentR := by
    dsimp [momentR]
    exact ((Complex.continuous_ofReal.pow 3).mul hcK2).mul hcInvR
  have hcA : Continuous momentA := by
    dsimp [momentA]
    exact ((Complex.continuous_ofReal.pow 3).mul hcK2).mul hcInvA
  have hsplit :
      (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) ^ 3 * k2 p * (invR p - invA p)) =
      (∫ p in (0 : ℝ)..pMax, momentR p) -
        ∫ p in (0 : ℝ)..pMax, momentA p := by
    calc
      _ = ∫ p in (0 : ℝ)..pMax, momentR p - momentA p := by
        apply intervalIntegral.integral_congr
        intro p _
        dsimp [momentR, momentA]
        ring
      _ = _ := intervalIntegral.integral_sub
        (hcR.intervalIntegrable 0 pMax) (hcA.intervalIntegrable 0 pMax)
  have hR := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_tracelessHessian
    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  have hA := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_tracelessHessian
    .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  have hdiff :
      (hbar : ℂ) ^ 2 *
        ((radius : ℂ) *
          (deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .retarded v m probeEnergy broadening disorderStrength hbar pMax r)) radius -
           deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .advanced v m probeEnergy broadening disorderStrength hbar pMax r)) radius) -
         (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius -
          deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius)) =
      -(radius : ℂ) * measure *
        ((∫ p in (0 : ℝ)..pMax, momentR p) -
          ∫ p in (0 : ℝ)..pMax, momentA p) := by
    calc
      _ = (hbar : ℂ) ^ 2 *
          ((radius : ℂ) *
            deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
              .retarded v m probeEnergy broadening disorderStrength hbar pMax r)) radius -
            deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
              .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius) -
        (hbar : ℂ) ^ 2 *
          ((radius : ℂ) *
            deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
              .advanced v m probeEnergy broadening disorderStrength hbar pMax r)) radius -
            deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
              .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius) := by ring
      _ = (-(radius : ℂ) * measure * ∫ p in (0 : ℝ)..pMax, momentR p) -
          (-(radius : ℂ) * measure * ∫ p in (0 : ℝ)..pMax, momentA p) := by
          rw [hR, hA]
      _ = _ := by ring
  calc
    (radius : ℂ) *
        finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax *
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      (radius : ℂ) * (2 * (v : ℂ) ^ 2 * factor * measure) *
        ((∫ p in (0 : ℝ)..pMax, momentR p) -
          ∫ p in (0 : ℝ)..pMax, momentA p) := by
          have hx := congrArg (fun z : ℂ => (radius : ℂ) * z) hk
          rw [hsplit] at hx
          convert hx using 1 <;> ring
    _ = _ := by
          have hx := congrArg (fun z : ℂ => -2 * (v : ℂ) ^ 2 * factor * z) hdiff
          convert hx.symm using 1 <;> ring



/-- The *actual* R/A Dyson propagator product at finite broadening is a
real radial Lorentzian denominator. The spectral center and width are
defined by the real/imaginary parts of the retarded Dyson denominator
at zero momentum, not by postulating clean or renormalized parameters. -/
private theorem gaussianCrossed_radialRAProduct_eq_realLorentzian
    (v m probeEnergy broadening disorderStrength hbar pMax p : ℝ)
    (hbroadening : broadening ≠ 0) :
    let D0 := finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      v m p probeEnergy broadening disorderStrength hbar pMax =
      (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ) := by
  dsimp only
  let D0 := finiteCutoffContinuumBornDysonDenominator
    .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
  let D := finiteCutoffContinuumBornDysonDenominator
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have hradial : D = D0 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) := by
    dsimp [D, D0]
    unfold finiteCutoffContinuumBornDysonDenominator
    push_cast
    ring
  have hstar : star D =
      finiteCutoffContinuumBornDysonDenominator
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    dsimp [D]
    simpa [SpectralSide.opposite] using
      (star_finiteCutoffContinuumBornDysonDenominator
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening)
  calc
    _ = D * star D := by
      rw [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul,
        ← hstar]
    _ = (Complex.normSq D : ℂ) := by
      simpa using (Complex.mul_conj D)
    _ = _ := by
      rw [hradial, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      push_cast
      ring

/-- The *physical* finite-broadening Gaussian-crossed K2 current is a
nonconstant Bessel-weighted **real Lorentzian radial integral**. The
effective center and width retain the actual cutoff-dependent Born-Dyson
self energy. This is the form needed before any on-shell concentration
argument; it does not silently take a regulator/disorder limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedInPlaneK2_eq_realLorentzian
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let D0 := finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let measure := (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    jxx - jyy =
      (2 * measure * (v : ℂ) ^ 2 * factor) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 3 *
            polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹ := by
  dsimp only
  let D0 := finiteCutoffContinuumBornDysonDenominator
    .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let kernel := fun p : ℝ =>
    (p : ℂ) ^ 3 * polarFourierSecondCosineAngularKernel (p * radius / hbar) *
      (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹
  have hdiag :=
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_ra_denominator_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax).2
  dsimp only at hdiag
  calc
    _ = measure * ∫ p in (0 : ℝ)..pMax,
        (2 * (v : ℂ) ^ 2 * factor) * kernel p := by
          rw [hdiag]
          congr 1
          apply intervalIntegral.integral_congr
          intro p _
          dsimp only
          rw [gaussianCrossed_radialRAProduct_eq_realLorentzian
            v m probeEnergy broadening disorderStrength hbar pMax p hbroadening]
          dsimp [D0, kernel, factor]
          push_cast
          ring
    _ = (2 * measure * (v : ℂ) ^ 2 * factor) *
          ∫ p in (0 : ℝ)..pMax, kernel p := by
            rw [intervalIntegral.integral_const_mul]
            ring
    _ = _ := rfl


/-- A quantitative **off-shell** estimate for the physical Gaussian-crossed
K2 Fourier kernel. If the radial momenta in [a,b] stay a fixed spectral
distance δ from the *actual finite-regulator* Dyson shell, the width-scaled
K2 contribution is bounded linearly by the imaginary Dyson width.
This is the needed tail estimate before using an on-shell Lorentzian
concentration theorem; no clean-spectrum substitution is made. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedK2_offShell_width_integral_norm_le
    (v m probeEnergy broadening disorderStrength hbar pMax radius a b δ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ pMax)
    (hδ : 0 < δ)
    (hsep : ∀ p ∈ Set.Icc a b,
      δ ≤ |(finiteCutoffContinuumBornDysonDenominator
        .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax).re -
        v ^ 2 * p ^ 2|) :
    let D0 := finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
    ‖(D0.im : ℂ) *
        ∫ p in a..b,
          (p : ℂ) ^ 3 *
            polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹‖ ≤
      (b - a) * (|D0.im| * pMax ^ 3 * (2 * Real.pi) / δ ^ 2) := by
  dsimp only
  let D0 := finiteCutoffContinuumBornDysonDenominator
    .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
  let weight : ℝ → ℂ := fun p =>
    (p : ℂ) ^ 3 * polarFourierSecondCosineAngularKernel (p * radius / hbar) *
      (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹
  let C : ℝ := |D0.im| * pMax ^ 3 * (2 * Real.pi) / δ ^ 2
  have hpMax : 0 ≤ pMax := le_trans (le_trans ha hab) hb
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hpoint (p : ℝ) (hp : p ∈ Set.Icc a b) :
      ‖(D0.im : ℂ) * weight p‖ ≤ C := by
    have hp0 : 0 ≤ p := le_trans ha hp.1
    have hpUpper : p ≤ pMax := le_trans hp.2 hb
    have hpow : p ^ 3 ≤ pMax ^ 3 := by gcongr
    let d : ℝ := (D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2
    have hsepAt : δ ≤ |D0.re - v ^ 2 * p ^ 2| := hsep p hp
    have hsquared : δ ^ 2 ≤ (D0.re - v ^ 2 * p ^ 2) ^ 2 := by
      have hprod : 0 ≤
          (|D0.re - v ^ 2 * p ^ 2| - δ) *
            (|D0.re - v ^ 2 * p ^ 2| + δ) :=
        mul_nonneg
          (sub_nonneg.mpr hsepAt)
          (add_nonneg (abs_nonneg (D0.re - v ^ 2 * p ^ 2)) hδ.le)
      nlinarith [sq_abs (D0.re - v ^ 2 * p ^ 2)]
    have hd : δ ^ 2 ≤ d := by
      dsimp [d]
      nlinarith [sq_nonneg D0.im]
    have hdPos : 0 < d := lt_of_lt_of_le hδsq hd
    have hinv : d⁻¹ ≤ (δ ^ 2)⁻¹ :=
      (inv_le_inv₀ hdPos hδsq).2 hd
    have hkernel :
        ‖polarFourierSecondCosineAngularKernel (p * radius / hbar)‖ ≤
          2 * Real.pi :=
      polarFourierSecondCosineAngularKernel_norm_le _
    have hnorm :
        ‖(D0.im : ℂ) * weight p‖ =
          |D0.im| * p ^ 3 *
            ‖polarFourierSecondCosineAngularKernel (p * radius / hbar)‖ * d⁻¹ := by
      change ‖(D0.im : ℂ) *
          ((p : ℂ) ^ 3 *
            polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (d : ℂ)⁻¹)‖ =
            |D0.im| * p ^ 3 *
              ‖polarFourierSecondCosineAngularKernel (p * radius / hbar)‖ * d⁻¹
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        norm_inv, abs_of_nonneg hp0, abs_of_pos hdPos]
      ring_nf
    rw [hnorm]
    dsimp [C]
    calc
      _ ≤ |D0.im| * pMax ^ 3 * (2 * Real.pi) * (δ ^ 2)⁻¹ := by
        gcongr
      _ = _ := by ring
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := C)
      (f := fun p => (D0.im : ℂ) * weight p)
      (by
        intro p hp
        apply hpoint p
        simpa [Set.uIcc_of_le hab] using (Set.uIoc_subset_uIcc hp))
  calc
    ‖(D0.im : ℂ) * ∫ p in a..b, weight p‖ =
      ‖∫ p in a..b, (D0.im : ℂ) * weight p‖ := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ C * |b - a| := hnorm
    _ = (b - a) * (|D0.im| * pMax ^ 3 * (2 * Real.pi) / δ ^ 2) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      dsimp [C]
      ring


/-- The **actual Dyson K2 off-shell spectral contribution vanishes in the
zero-width limit** on any fixed radial interval uniformly separated from
the moving Dyson shell. This is a genuine asymptotic statement: the
Lorentzian width and center may both depend on arbitrary regulators,
including the ordered broadening/disorder trajectory. Only their
explicitly stated width convergence and spectral separation are used. -/
theorem tendsto_finiteCutoffContinuumBornDysonGaussianCrossedK2_offShell_width_integral_zero
    {ι : Type*} {l : Filter ι}
    (v m probeEnergy hbar pMax radius a b δ : ℝ)
    (broadening disorderStrength : ι → ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ pMax)
    (hδ : 0 < δ)
    (hwidth : Tendsto
      (fun t =>
        (finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
          hbar pMax).im)
      l (nhds 0))
    (hsep : ∀ᶠ t in l, ∀ p ∈ Set.Icc a b,
      δ ≤ |(finiteCutoffContinuumBornDysonDenominator
        .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
        hbar pMax).re - v ^ 2 * p ^ 2|) :
    Tendsto
      (fun t =>
        let D0 := finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
          hbar pMax
        (D0.im : ℂ) *
          ∫ p in a..b,
            (p : ℂ) ^ 3 *
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹)
      l (nhds 0) := by
  let D0 : ι → ℂ := fun t =>
    finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
      hbar pMax
  let tail : ι → ℂ := fun t =>
    ((D0 t).im : ℂ) *
      ∫ p in a..b,
        (p : ℂ) ^ 3 *
          polarFourierSecondCosineAngularKernel (p * radius / hbar) *
          ((((D0 t).re - v ^ 2 * p ^ 2) ^ 2 + (D0 t).im ^ 2 : ℝ) : ℂ)⁻¹
  have hw : Tendsto (fun t => |(D0 t).im|) l (nhds 0) := by
    simpa only [D0, abs_zero] using hwidth.abs
  let C : ℝ := (b - a) * (pMax ^ 3 * (2 * Real.pi) / δ ^ 2)
  have hupper : Tendsto (fun t => |(D0 t).im| * C) l (nhds 0) := by
    simpa using hw.mul_const C
  have hnorm : Tendsto (fun t => ‖tail t‖) l (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hupper
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg (tail t))
    · filter_upwards [hsep] with t ht
      have hbound :=
        finiteCutoffContinuumBornDysonGaussianCrossedK2_offShell_width_integral_norm_le
          v m probeEnergy (broadening t) (disorderStrength t)
          hbar pMax radius a b δ ha hab hb hδ ht
      calc
        ‖tail t‖ ≤
            (b - a) * (|(D0 t).im| * pMax ^ 3 * (2 * Real.pi) / δ ^ 2) := by
              simpa only [tail, D0] using hbound
        _ = |(D0 t).im| * C := by
          dsimp [C]
          ring
  change Tendsto tail l (nhds 0)
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm


/-- The off-shell part of the *dressed physical K2 crossed current* has
zero width-normalized limit whenever the actual ladder factor approaches
a finite value. This keeps the original Fourier measure and v² factor.
The needed finite-ladder limit is stated explicitly rather than silently
inferred from the spectral width limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonGaussianCrossedK2_offShell_dressedCurrent_zero
    {ι : Type*} {l : Filter ι}
    (v m probeEnergy hbar pMax radius a b δ : ℝ)
    (broadening disorderStrength : ι → ℝ) (factorLimit : ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ pMax)
    (hδ : 0 < δ)
    (hwidth : Tendsto
      (fun t =>
        (finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
          hbar pMax).im)
      l (nhds 0))
    (hsep : ∀ᶠ t in l, ∀ p ∈ Set.Icc a b,
      δ ≤ |(finiteCutoffContinuumBornDysonDenominator
        .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
        hbar pMax).re - v ^ 2 * p ^ 2|)
    (hfactor : Tendsto
      (fun t => finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
        v m probeEnergy (broadening t) (disorderStrength t) hbar pMax)
      l (nhds factorLimit)) :
    Tendsto
      (fun t =>
        let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy (broadening t) (disorderStrength t) hbar pMax
        let D0 := finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
          hbar pMax
        ((D0.im : ℂ) *
            (2 * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (v : ℂ) ^ 2 * factor)) *
          ∫ p in a..b,
            (p : ℂ) ^ 3 *
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹)
      l (nhds 0) := by
  let D0 : ι → ℂ := fun t =>
    finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy (broadening t) (disorderStrength t)
      hbar pMax
  let tail : ι → ℂ := fun t =>
    ((D0 t).im : ℂ) *
      ∫ p in a..b,
        (p : ℂ) ^ 3 *
          polarFourierSecondCosineAngularKernel (p * radius / hbar) *
          ((((D0 t).re - v ^ 2 * p ^ 2) ^ 2 + (D0 t).im ^ 2 : ℝ) : ℂ)⁻¹
  let dressed : ι → ℂ := fun t =>
    (2 * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * (v : ℂ) ^ 2) *
      finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
        v m probeEnergy (broadening t) (disorderStrength t) hbar pMax
  have htail :
      Tendsto tail l (nhds 0) := by
    exact tendsto_finiteCutoffContinuumBornDysonGaussianCrossedK2_offShell_width_integral_zero
      v m probeEnergy hbar pMax radius a b δ broadening disorderStrength
      ha hab hb hδ hwidth hsep
  have hdressed : Tendsto dressed l
      (nhds ((2 * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (v : ℂ) ^ 2) * factorLimit)) :=
    tendsto_const_nhds.mul hfactor
  have hresult : Tendsto (fun t => dressed t * tail t) l (nhds 0) := by
    simpa using hdressed.mul htail
  apply hresult.congr'
  exact Filter.Eventually.of_forall fun t => by
    dsimp [tail, dressed, D0]
    ring


/-- Exact finite-interval *energy-shell* substitution for the physical
traceless crossed-current harmonic. The second-cosine angular kernel
is real on the physical radial axis, so the real-valued interval
substitution theorem gives the exact Jacobian of u=v²p²-A.

No regulator/disorder/UV limit is taken, and no imaginary part or
Fourier normalization is discarded. -/
private theorem gaussianCrossed_K2_radialLorentzian_eq_energyShell
    (v hbar pMax radius A B : ℝ)
    (hv : v ≠ 0) (hpMax : 0 ≤ pMax) (hB : B ≠ 0) :
    (((2 * v ^ 4 : ℝ) : ℂ)) * (B : ℂ) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 3 *
            polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            ((((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 : ℝ) : ℂ))⁻¹ =
      ∫ offset in -A..(v ^ 2 * pMax ^ 2 - A),
        (Lorentzian.spectralKernel offset B : ℂ) *
          ((A + offset : ℝ) : ℂ) *
          polarFourierSecondCosineAngularKernel
            (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar) := by
  let k2Real : ℝ → ℝ :=
    fun z => (polarFourierSecondCosineAngularKernel z).re
  have hrealK2 (z : ℝ) :
      polarFourierSecondCosineAngularKernel z = (k2Real z : ℂ) := by
    have him : (polarFourierSecondCosineAngularKernel z).im = 0 :=
      Complex.conj_eq_iff_im.mp (polarFourierSecondCosineAngularKernel_conj z)
    apply Complex.ext
    · rfl
    · simpa [k2Real, him]
  let f : ℝ → ℝ := fun p => v ^ 2 * p ^ 2 - A
  let df : ℝ → ℝ := fun p => 2 * v ^ 2 * p
  let g : ℝ → ℝ := fun offset =>
    Lorentzian.spectralKernel offset B * (A + offset) *
      k2Real (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar)
  have harg : Continuous (fun offset : ℝ =>
      Real.sqrt ((A + offset) / v ^ 2) * radius / hbar) := by fun_prop
  have hcontinuousK2 : Continuous k2Real :=
    Complex.continuous_re.comp continuous_polarFourierSecondCosineAngularKernel
  have hg : Continuous g := by
    dsimp [g]
    exact ((Lorentzian.continuous_spectralKernel_fixed_broadening B hB).mul
      (continuous_const.add continuous_id)).mul
        (hcontinuousK2.comp harg)
  have hdf : Continuous df := by
    dsimp [df]
    fun_prop
  have hderiv (p : ℝ) : HasDerivAt f (df p) p := by
    convert ((((hasDerivAt_id p).pow 2).const_mul (v ^ 2)).sub_const A) using 1
    · funext t
      simp [f, Pi.pow_apply]
    · dsimp [df]
      ring
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := pMax) (f := f) (f' := df) (g := g)
    (fun p _ => hderiv p) hdf.continuousOn hg.continuousOn
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hpoint (p : ℝ) (hp : 0 ≤ p) :
      g (f p) * df p =
        (2 * v ^ 4) * B *
          (p ^ 3 * k2Real (p * radius / hbar) /
            ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2)) := by
    have hsquare : (A + (v ^ 2 * p ^ 2 - A)) / v ^ 2 = p ^ 2 := by
      field_simp [hv2]
      ring
    have hsqrt :
        Real.sqrt ((A + (v ^ 2 * p ^ 2 - A)) / v ^ 2) = p := by
      rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
    have hden :
        B ^ 2 + (v ^ 2 * p ^ 2 - A) ^ 2 =
          (A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 := by ring
    dsimp [f, df, g, Lorentzian.spectralKernel]
    rw [hsqrt, hden]
    simp only [div_eq_mul_inv]
    ring
  have hreal :
      (2 * v ^ 4) * B *
        ∫ p in (0 : ℝ)..pMax,
          p ^ 3 * k2Real (p * radius / hbar) /
            ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) =
        ∫ offset in -A..(v ^ 2 * pMax ^ 2 - A),
          Lorentzian.spectralKernel offset B * (A + offset) *
            k2Real (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar) := by
    calc
      _ = ∫ p in (0 : ℝ)..pMax, g (f p) * df p := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro p hp
        have hpNonneg : 0 ≤ p := by
          have hi : p ∈ Set.Icc (0 : ℝ) pMax := by
            simpa [Set.uIcc_of_le hpMax] using hp
          exact hi.1
        exact (hpoint p hpNonneg).symm
      _ = ∫ offset in f 0..f pMax, g offset := by
        simpa only [Function.comp_apply] using hsub
      _ = _ := by
        dsimp [f, g]
        simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  have hcastP :
      (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) ^ 3 *
          polarFourierSecondCosineAngularKernel (p * radius / hbar) *
          ((((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2 : ℝ) : ℂ))⁻¹) =
      ((∫ p in (0 : ℝ)..pMax,
          p ^ 3 * k2Real (p * radius / hbar) /
            ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) : ℝ) : ℂ) := by
    calc
      _ = ∫ p in (0 : ℝ)..pMax,
            ((p ^ 3 * k2Real (p * radius / hbar) /
              ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro p _
        dsimp only
        rw [hrealK2]
        push_cast
        ring
      _ = _ := RCLike.intervalIntegral_ofReal (𝕜 := ℂ) (μ := volume)
        (f := fun p : ℝ => p ^ 3 * k2Real (p * radius / hbar) /
          ((A - v ^ 2 * p ^ 2) ^ 2 + B ^ 2))
        (a := 0) (b := pMax)
  have hcastU :
      (∫ offset in -A..(v ^ 2 * pMax ^ 2 - A),
        (Lorentzian.spectralKernel offset B : ℂ) *
          ((A + offset : ℝ) : ℂ) *
          polarFourierSecondCosineAngularKernel
            (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar)) =
      ((∫ offset in -A..(v ^ 2 * pMax ^ 2 - A),
          Lorentzian.spectralKernel offset B * (A + offset) *
            k2Real (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar) : ℝ) : ℂ) := by
    calc
      _ = ∫ offset in -A..(v ^ 2 * pMax ^ 2 - A),
          ((Lorentzian.spectralKernel offset B * (A + offset) *
            k2Real (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro offset _
        dsimp only
        rw [hrealK2]
        push_cast
        ring
      _ = _ := RCLike.intervalIntegral_ofReal (𝕜 := ℂ) (μ := volume)
        (f := fun offset : ℝ => Lorentzian.spectralKernel offset B * (A + offset) *
          k2Real (Real.sqrt ((A + offset) / v ^ 2) * radius / hbar))
        (a := -A) (b := v ^ 2 * pMax ^ 2 - A)
  rw [hcastP, hcastU]
  exact_mod_cast hreal

/-- The **actual finite-cutoff dressed crossed K2 current**, multiplied by
the actual Dyson width, is *exactly* a spectral Lorentzian convolution
on the physical energy shell. It is this integral, not an independently
declared reference kernel, whose eventual on-shell limit must be proved.

No clean-spectrum replacement or order interchange is made. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedInPlaneK2_width_eq_energyShell
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hv : v ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax)
    (hwidth : (finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax).im ≠ 0) :
    let D0 := finiteCutoffContinuumBornDysonDenominator
      .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let measure := (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    (((2 * v ^ 4 : ℝ) : ℂ)) * (D0.im : ℂ) * (jxx - jyy) =
      (2 * measure * (v : ℂ) ^ 2 * factor) *
        ∫ offset in -D0.re..(v ^ 2 * pMax ^ 2 - D0.re),
          (Lorentzian.spectralKernel offset D0.im : ℂ) *
            ((D0.re + offset : ℝ) : ℂ) *
            polarFourierSecondCosineAngularKernel
              (Real.sqrt ((D0.re + offset) / v ^ 2) * radius / hbar) := by
  dsimp only
  let D0 := finiteCutoffContinuumBornDysonDenominator
    .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hj := finiteCutoffContinuumBornDysonGaussianCrossedInPlaneK2_eq_realLorentzian
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hsub := gaussianCrossed_K2_radialLorentzian_eq_energyShell
    v hbar pMax radius D0.re D0.im hv hpMax hwidth
  dsimp only at hj hsub
  calc
    (((2 * v ^ 4 : ℝ) : ℂ)) * (D0.im : ℂ) *
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
         finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
      (2 * measure * (v : ℂ) ^ 2 * factor) *
        (((2 * v ^ 4 : ℝ) : ℂ)) * (D0.im : ℂ) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) ^ 3 *
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              (((D0.re - v ^ 2 * p ^ 2) ^ 2 + D0.im ^ 2 : ℝ) : ℂ)⁻¹ := by
            rw [hj]
            ring
    _ = (2 * measure * (v : ℂ) ^ 2 * factor) *
          ∫ offset in -D0.re..(v ^ 2 * pMax ^ 2 - D0.re),
            (Lorentzian.spectralKernel offset D0.im : ℂ) *
              ((D0.re + offset : ℝ) : ℂ) *
              polarFourierSecondCosineAngularKernel
                (Real.sqrt ((D0.re + offset) / v ^ 2) * radius / hbar) := by
            rw [← hsub]
            ring


/-- A fixed positive offset window eventually lies strictly inside the
actual moving Born-Dyson spectral interval after the external broadening
boundary, for sufficiently weak positive disorder.

The clean on-shell energy is E0 = ε²−m². This is the endpoint control
needed to split the physical finite-cutoff energy-shell integral into a
centered window and two off-shell tails. -/
theorem eventually_finiteCutoffContinuumBornDysonGaussianCrossedK2_cleanWindow_in_boundaryShell
    (v m probeEnergy hbar pMax windowRadius : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hwindowLower : windowRadius < probeEnergy ^ 2 - m ^ 2)
    (hwindowUpper :
      windowRadius < v ^ 2 * pMax ^ 2 - (probeEnergy ^ 2 - m ^ 2)) :
    ∀ᶠ W : ℝ in nhdsWithin 0 (Set.Ioi 0),
      -(finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .retarded v m 0 probeEnergy W hbar pMax).re < -windowRadius ∧
      windowRadius < v ^ 2 * pMax ^ 2 -
        (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
          .retarded v m 0 probeEnergy W hbar pMax).re := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let A : ℝ → ℝ := fun W =>
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m 0 probeEnergy W hbar pMax).re
  have hcenter : Tendsto A l (nhds (probeEnergy ^ 2 - m ^ 2)) :=
    (tendsto_finiteCutoffContinuumBornDysonBoundarySpectralShell_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff).1
  have hright : probeEnergy ^ 2 - m ^ 2 <
      v ^ 2 * pMax ^ 2 - windowRadius := by linarith
  have hinside := hcenter.eventually (Ioo_mem_nhds hwindowLower hright)
  filter_upwards [hinside] with W hW
  have hA : windowRadius < A W ∧ A W < v ^ 2 * pMax ^ 2 - windowRadius := by
    simpa only [Set.mem_Ioo] using hW
  dsimp only [A] at hA
  constructor <;> linarith

/-- The actual positive Born-Dyson width, along the physical
zero-external-broadening then weak-disorder trajectory, concentrates
the nonconstant second Fourier harmonic in a fixed centered window.

The Bessel weight is evaluated at the clean shell E0=ε²−m² in this
theorem; the distinct moving-center correction and asymmetric tails
still need to be controlled for the full crossed-current limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonGaussianCrossedK2_cleanCenteredWindow
    (v m probeEnergy hbar pMax radius windowRadius : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hwindowPos : 0 < windowRadius) :
    let E0 := probeEnergy ^ 2 - m ^ 2
    let width := fun W : ℝ =>
      (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
        .retarded v m 0 probeEnergy W hbar pMax).im
    Tendsto
      (fun W : ℝ =>
        ∫ offset in -windowRadius..windowRadius,
          (Lorentzian.spectralKernel offset (width W) : ℂ) *
            ((E0 + offset : ℝ) : ℂ) *
            polarFourierSecondCosineAngularKernel
              (Real.sqrt ((E0 + offset) / v ^ 2) * radius / hbar))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi •
        ((E0 : ℂ) *
          polarFourierSecondCosineAngularKernel
            (Real.sqrt (E0 / v ^ 2) * radius / hbar)))) := by
  dsimp only
  let E0 : ℝ := probeEnergy ^ 2 - m ^ 2
  let width : ℝ → ℝ := fun W =>
    (finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary
      .retarded v m 0 probeEnergy W hbar pMax).im
  let factor : ℝ × ℝ → ℂ := fun q =>
    ((E0 + q.1 : ℝ) : ℂ) *
      polarFourierSecondCosineAngularKernel
        (Real.sqrt ((E0 + q.1) / v ^ 2) * radius / hbar)
  have harg : Continuous (fun q : ℝ × ℝ =>
      Real.sqrt ((E0 + q.1) / v ^ 2) * radius / hbar) := by
    fun_prop
  have hfactor : Continuous factor := by
    dsimp only [factor]
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul
      (continuous_polarFourierSecondCosineAngularKernel.comp harg)
  have hrectangle : ∃ etaMax : ℝ, 0 < etaMax ∧ ContinuousOn factor
      (Set.Icc (-windowRadius) windowRadius ×ˢ Set.Icc (0 : ℝ) etaMax) :=
    ⟨1, by norm_num, hfactor.continuousOn⟩
  have hPole := Lorentzian.tendsto_integral_spectralKernel_mul
    factor windowRadius hwindowPos hrectangle
  have hWidth : Tendsto width
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    (tendsto_finiteCutoffContinuumBornDysonBoundarySpectralShell_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff).2.1
  have hResult := hPole.comp hWidth
  simpa only [factor, width, E0, add_zero, Function.comp_def, mul_assoc] using hResult

end

end QuantumTheory.Models.MassiveDirac
