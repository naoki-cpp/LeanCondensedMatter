import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite-cutoff massive-Dirac scalar radial Green generator

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

/-- At finite broadening, the scalar Dyson resolvent weight is a continuous
function of the radial momentum, including both endpoints of the cutoff
integral. -/
private theorem continuous_finiteCutoffContinuumBornDysonScalarGreenWeight
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Continuous fun p : ℝ =>
      (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
  have hden : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
    intro p
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hcont : Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    fun_prop
  exact (Complex.continuous_ofReal.comp continuous_id).mul (hcont.inv₀ hden)

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
    (continuous_finiteCutoffContinuumBornDysonScalarGreenWeight
      side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax) pMax hbar radius
  convert h.const_mul (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) using 1
  · funext r
    rfl

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
  have hpoint :
      (∫ p in (0 : ℝ)..pMax, kernel p) =
        ∫ p in (0 : ℝ)..pMax, coeff *
          ((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            polarFourierZerothAngularKernel (p * radius / hbar)) := by
    apply intervalIntegral.integral_congr
    intro p _
    exact hkernel p
  rw [hpoint, intervalIntegral.integral_const_mul]
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
    have hunit : (-Complex.I) * Complex.I = (1 : ℂ) := by
      calc
        _ = -(Complex.I ^ 2) := by ring
        _ = 1 := by rw [Complex.I_sq]; ring
    calc
      _ = ((-Complex.I) * Complex.I) *
          ((p : ℂ) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
            (((hbar * v : ℝ) : ℂ)) *
            ((p / hbar : ℝ) : ℂ) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar)) := by
        rw [hunit]
        ring
      _ = _ := by ring
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
