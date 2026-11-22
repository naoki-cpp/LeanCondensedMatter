import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.RadialGreen
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar radial Fourier generator for the Born-Dyson Green function

A single scalar radial Fourier integral generates the finite-broadening
Born--Dyson Green matrix: its scalar and z-Pauli components are obtained by
multiplication by the effective energy and mass, while its radial derivative
reproduces the x-Pauli component with the physical Fourier factor
`-i ℏ v`. This reduction is exact at fixed finite momentum cutoff and
nonzero external broadening, before any ultraviolet, disorder, or
broadening limit. In particular, it does not assume an unformalized
second-kind Bessel or Hankel representation.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- Finite-cutoff scalar resolvent Fourier transform, including its physical
momentum measure. This is the scalar generator of the radial Dirac Green
matrix, not the coefficient of the identity matrix itself. -/
noncomputable def finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        polarFourierZerothAngularKernel (p * radius / hbar)

/-- Differentiation in the signed radial coordinate commutes with the
regulated scalar Green Fourier integral; the resulting channel is K₁. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    HasDerivAt
      (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax r)
      ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          ((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
            (Complex.I * ((p / hbar : ℝ) : ℂ) *
              polarFourierFirstCosineAngularKernel (p * radius / hbar)))
      radius := by
  have h := hasDerivAt_integral_polarFourierZerothAngularKernel
    (fun p : ℝ => (p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)
    ((Complex.continuous_ofReal.comp continuous_id).mul
      (continuous_finiteCutoffContinuumBornDysonDenominator_inv_radial
        side v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax)) pMax hbar radius
  convert h.const_mul (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) using 1
  · funext r
    rfl

/-- The second derivative of the *physical* finite-cutoff radial Dyson
Green generator contains both the K0 and K2 Fourier harmonics. This
derivative is taken before removing cutoff or broadening. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt_deriv
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    HasDerivAt
      (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax r))
      ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          ((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            (Complex.I * ((p / hbar : ℝ) : ℂ))) *
            (((p / hbar : ℝ) : ℂ) *
              ((Complex.I / 2) *
                (polarFourierZerothAngularKernel (p * radius / hbar) +
                  polarFourierSecondCosineAngularKernel (p * radius / hbar)))))
      radius := by
  let weight : ℝ → ℂ := fun p =>
    ((p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
      (Complex.I * ((p / hbar : ℝ) : ℂ))
  have hcont : Continuous weight := by
    dsimp [weight]
    exact ((Complex.continuous_ofReal.mul
      (continuous_finiteCutoffContinuumBornDysonDenominator_inv_radial
        side v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax)).mul
      (continuous_const.mul
        (Complex.continuous_ofReal.comp (by fun_prop : Continuous (fun p : ℝ => p / hbar)))))
  have h := (hasDerivAt_integral_polarFourierFirstCosineAngularKernel
    weight hcont pMax hbar radius).const_mul
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
  convert h using 1
  · funext r
    rw [(finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt
      side v m probeEnergy broadening disorderStrength hbar pMax r
      hbroadening hdisorder hpMax).deriv]
    congr 1
    apply intervalIntegral.integral_congr
    intro p _
    dsimp [weight]
    ring

/-- The traceless radial Hessian of the actual Dyson scalar generator
is precisely its K2 Fourier harmonic. Multiplication by the signed
radius avoids an artificial r ≠ 0 hypothesis; no asymptotic radial or
momentum integral is differentiated. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_tracelessHessian
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0) (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    (hbar : ℂ) ^ 2 *
      ((radius : ℂ) *
          deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            side v m probeEnergy broadening disorderStrength hbar pMax r)) radius -
        deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax r) radius) =
      -(radius : ℂ) * (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 3 * polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
  let denInv : ℝ → ℂ := fun p =>
    (finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
  let ratio : ℝ → ℂ := fun p => ((p / hbar : ℝ) : ℂ)
  let k0 : ℝ → ℂ := fun p => polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 : ℝ → ℂ := fun p => polarFourierFirstCosineAngularKernel (p * radius / hbar)
  let k2 : ℝ → ℂ := fun p => polarFourierSecondCosineAngularKernel (p * radius / hbar)
  let first : ℝ → ℂ := fun p =>
    ((p : ℂ) * denInv p) * (Complex.I * ratio p * k1 p)
  let second : ℝ → ℂ := fun p =>
    (((p : ℂ) * denInv p) * (Complex.I * ratio p)) *
      (ratio p * ((Complex.I / 2) * (k0 p + k2 p)))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hden : Continuous denInv :=
    continuous_finiteCutoffContinuumBornDysonDenominator_inv_radial
      side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hratio : Continuous ratio :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hk0 : Continuous k0 :=
    continuous_polarFourierZerothAngularKernel.comp (by fun_prop)
  have hk1 : Continuous k1 :=
    continuous_polarFourierFirstCosineAngularKernel.comp (by fun_prop)
  have hk2 : Continuous k2 :=
    continuous_polarFourierSecondCosineAngularKernel.comp (by fun_prop)
  have hfirst : Continuous first := by
    dsimp [first]
    exact (Complex.continuous_ofReal.mul hden).mul
      ((continuous_const.mul hratio).mul hk1)
  have hsecond : Continuous second := by
    dsimp [second]
    exact ((Complex.continuous_ofReal.mul hden).mul
      (continuous_const.mul hratio)).mul
        (hratio.mul (continuous_const.mul (hk0.add hk2)))
  have hfirstInt : IntervalIntegrable first volume 0 pMax :=
    hfirst.intervalIntegrable 0 pMax
  have hsecondInt : IntervalIntegrable second volume 0 pMax :=
    hsecond.intervalIntegrable 0 pMax
  have h1 :
      deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax r) radius =
        measure * ∫ p in (0 : ℝ)..pMax, first p := by
    simpa only [first, denInv, ratio, k1, measure] using
      (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt
        side v m probeEnergy broadening disorderStrength hbar pMax radius
        hbroadening hdisorder hpMax).deriv
  have h2 :
      deriv (deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax r)) radius =
        measure * ∫ p in (0 : ℝ)..pMax, second p := by
    simpa only [second, denInv, ratio, k0, k2, measure] using
      (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt_deriv
        side v m probeEnergy broadening disorderStrength hbar pMax radius
        hbroadening hdisorder hpMax).deriv
  have hcombine :
      (radius : ℂ) * (∫ p in (0 : ℝ)..pMax, second p) -
          ∫ p in (0 : ℝ)..pMax, first p =
        ∫ p in (0 : ℝ)..pMax, (radius : ℂ) * second p - first p := by
    calc
      _ = (∫ p in (0 : ℝ)..pMax, (radius : ℂ) * second p) -
            ∫ p in (0 : ℝ)..pMax, first p := by
              rw [intervalIntegral.integral_const_mul]
      _ = _ := (intervalIntegral.integral_sub
        ((continuous_const.mul hsecond).intervalIntegrable 0 pMax)
        hfirstInt).symm
  have hpoint (p : ℝ) :
      (hbar : ℂ) ^ 2 * ((radius : ℂ) * second p - first p) =
        -(radius : ℂ) * (p : ℂ) ^ 3 * k2 p * denInv p := by
    have hrat : (hbar : ℂ) * ratio p = (p : ℂ) := by
      dsimp [ratio]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hhbar]
    have hz : ((p * radius / hbar : ℝ) : ℂ) = (radius : ℂ) * ratio p := by
      dsimp [ratio]
      push_cast
      ring
    have hrec :=
      polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
        (p * radius / hbar)
    have hk1val : k1 p =
        (Complex.I * (radius : ℂ) * ratio p * (k0 p - k2 p)) / 2 := by
      apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
      calc
        k1 p * 2 = 2 * polarFourierFirstCosineAngularKernel (p * radius / hbar) := by
          dsimp [k1]
          ring
        _ = Complex.I * ((p * radius / hbar : ℝ) : ℂ) *
              (polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar)) := hrec
        _ = Complex.I * (radius : ℂ) * ratio p * (k0 p - k2 p) := by
          rw [hz]
          dsimp [k0, k2]
          ring
    have hrat2 : (hbar : ℂ) ^ 2 * ratio p ^ 2 = (p : ℂ) ^ 2 := by
      calc
        _ = ((hbar : ℂ) * ratio p) ^ 2 := by ring
        _ = (p : ℂ) ^ 2 := by rw [hrat]
    dsimp only [first, second]
    rw [hk1val]
    calc
      _ = (hbar : ℂ) ^ 2 * (-(radius : ℂ) * ratio p ^ 2 *
            k2 p * ((p : ℂ) * denInv p)) := by
          ring_nf
          simp only [Complex.I_sq]
          ring
      _ = _ := by
          calc
            _ = -(radius : ℂ) * ((hbar : ℂ) ^ 2 * ratio p ^ 2) *
                  k2 p * ((p : ℂ) * denInv p) := by ring
            _ = _ := by rw [hrat2]; ring
  rw [h1, h2]
  calc
    (hbar : ℂ) ^ 2 *
        ((radius : ℂ) * (measure * ∫ p in (0 : ℝ)..pMax, second p) -
          measure * ∫ p in (0 : ℝ)..pMax, first p) =
      measure * ((hbar : ℂ) ^ 2 *
        ((radius : ℂ) * (∫ p in (0 : ℝ)..pMax, second p) -
          ∫ p in (0 : ℝ)..pMax, first p)) := by ring
    _ = measure * ((hbar : ℂ) ^ 2 *
          ∫ p in (0 : ℝ)..pMax, (radius : ℂ) * second p - first p) := by rw [hcombine]
    _ = measure * ∫ p in (0 : ℝ)..pMax,
          (hbar : ℂ) ^ 2 * ((radius : ℂ) * second p - first p) := by
          rw [intervalIntegral.integral_const_mul]
    _ = measure * ∫ p in (0 : ℝ)..pMax,
          -(radius : ℂ) * (p : ℂ) ^ 3 * k2 p * denInv p := by
          congr 1
          apply intervalIntegral.integral_congr
          intro p _
          exact hpoint p
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      dsimp [measure, denInv, k2]
      ring

/-- A model-local linearity bridge for radial Green coefficients. The
normalization is carried once by the scalar generator, while a constant
effective spectral coefficient factors outside the *finite* momentum
integral. Both the identity and the hypotheses are independent of the
Pauli channel that supplies `kernel`. -/
private theorem finiteCutoffContinuumBornDyson_radialKernel_eq_scaledGenerator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (coeff : ℂ) (kernel : ℝ → ℂ)
    (hkernel : ∀ p : ℝ, kernel p =
      coeff *
        ((p : ℂ) *
          (finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
          polarFourierZerothAngularKernel (p * radius / hbar))) :
    (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      (∫ p in (0 : ℝ)..pMax, kernel p) =
      coeff * finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax radius := by
  simp_rw [hkernel]
  rw [intervalIntegral.integral_const_mul]
  dsimp [finiteCutoffContinuumBornDysonRadialScalarGreenGenerator]
  ring

/-- The diagonal scalar Green component is the effective Dyson energy
times the common radial scalar generator. -/
theorem finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_generator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax radius := by
  let energy := finiteCutoffContinuumBornEffectiveEnergy
    side v m probeEnergy broadening disorderStrength hbar pMax
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenScalarKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p :=
      finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
        side v m probeEnergy broadening disorderStrength hbar pMax radius
        hbroadening hdisorder hpMax
    _ = energy * finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax radius := by
      apply finiteCutoffContinuumBornDyson_radialKernel_eq_scaledGenerator
      intro p
      dsimp [energy, finiteCutoffContinuumBornDysonRadialGreenScalarKernel,
        finiteCutoffContinuumBornDysonRadialPauliData,
        finiteCutoffContinuumBornDysonScalarCoefficient]
      ring

/-- The z-Pauli Green component is the effective Dyson mass times the
same scalar radial Fourier generator. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_z_eq_generator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .z
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening disorderStrength hbar pMax radius := by
  let mass := finiteCutoffContinuumBornEffectiveMass
    side v m probeEnergy broadening disorderStrength hbar pMax
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenPauliKernel .z
            side v m probeEnergy broadening disorderStrength hbar pMax radius p :=
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
        .z side v m probeEnergy broadening disorderStrength hbar pMax radius
        hbroadening hdisorder hpMax
    _ = mass * finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax radius := by
      apply finiteCutoffContinuumBornDyson_radialKernel_eq_scaledGenerator
      intro p
      dsimp [mass, finiteCutoffContinuumBornDysonRadialGreenPauliKernel,
        finiteCutoffContinuumBornDysonRadialPauliData,
        finiteCutoffContinuumBornDysonPauliCoefficient,
        InternalSpace.pauliAxisComponent]
      ring

/-- At finite broadening and finite momentum cutoff, the in-plane radial
Green component is the radial derivative of the **same** scalar generator.
This exact first-order Dirac factorization retains the Fourier `ℏ` scale;
it does not use a Hankel function, infinite cutoff, or a contact-term
assumption. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax r) radius := by
  let d : ℝ → ℂ := fun p =>
    ((p : ℂ) *
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) *
    (Complex.I * ((p / hbar : ℝ) : ℂ) *
      polarFourierFirstCosineAngularKernel (p * radius / hbar))
  let alpha : ℂ := -Complex.I * (((hbar * v : ℝ) : ℂ))
  have hratio (p : ℝ) :
      (((hbar * v : ℝ) : ℂ)) * ((p / hbar : ℝ) : ℂ) =
        (((v * p : ℝ) : ℂ)) := by
    push_cast
    field_simp [hhbar]
  have hpoint (p : ℝ) :
      finiteCutoffContinuumBornDysonRadialGreenPauliKernel .x
        side v m probeEnergy broadening disorderStrength hbar pMax radius p =
        alpha * d p := by
    dsimp [alpha, d, finiteCutoffContinuumBornDysonRadialGreenPauliKernel,
      finiteCutoffContinuumBornDysonRadialPauliData,
      finiteCutoffContinuumBornDysonPauliCoefficient,
      InternalSpace.pauliAxisComponent]
    rw [show (((v * p : ℝ) : ℂ)) =
      (((hbar * v : ℝ) : ℂ)) * ((p / hbar : ℝ) : ℂ) from (hratio p).symm]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hderiv := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_hasDerivAt
    side v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  rw [hderiv.deriv]
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenPauliKernel .x
            side v m probeEnergy broadening disorderStrength hbar pMax radius p :=
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
        .x side v m probeEnergy broadening disorderStrength hbar pMax radius
        hbroadening hdisorder hpMax
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax, alpha * d p := by
      congr 1
      apply intervalIntegral.integral_congr
      intro p _
      exact hpoint p
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      dsimp [alpha, d]
      ring

/-- The full finite-cutoff radial Born--Dyson Dirac Green matrix is generated
by a single scalar Fourier integral: the scalar and out-of-plane channels
multiply the generator, while the in-plane Dirac term differentiates it.
This is the exact matrix-level bridge needed before identifying the
scalar kernel with a branch-dependent Hankel/Y-Bessel boundary value. -/
theorem finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_eq_scalarGenerator
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax radius) •
        (1 : Matrix2) +
      ((-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax r) radius) •
        InternalSpace.pauliX +
      (finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
          side v m probeEnergy broadening disorderStrength hbar pMax radius) •
        InternalSpace.pauliZ := by
  let G : Matrix2 := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
    side v m probeEnergy broadening disorderStrength hbar pMax radius
  have hs := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_generator
    side v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hx := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    side v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  have hy := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_y_eq_zero
    side v m probeEnergy broadening disorderStrength hbar pMax radius
  have hz := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_z_eq_generator
    side v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  calc
    _ = InternalSpace.pauliScalarCoefficient G • (1 : Matrix2) +
        InternalSpace.pauliCombination (InternalSpace.pauliVectorCoefficient G) :=
      InternalSpace.eq_pauliAffine_coefficients G
    _ = _ := by
      rw [InternalSpace.pauliCombination_eq_components]
      simp only [← add_assoc]
      change
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
            side v m probeEnergy broadening disorderStrength hbar pMax radius •
            (1 : Matrix2) +
          (finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
              side v m probeEnergy broadening disorderStrength hbar pMax radius) •
            InternalSpace.pauliX +
          (finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .y
              side v m probeEnergy broadening disorderStrength hbar pMax radius) •
            InternalSpace.pauliY +
          (finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .z
              side v m probeEnergy broadening disorderStrength hbar pMax radius) •
            InternalSpace.pauliZ = _
      rw [hs, hx, hy, hz]
      simp


end

end MassiveDirac
end Models
end QuantumTheory
