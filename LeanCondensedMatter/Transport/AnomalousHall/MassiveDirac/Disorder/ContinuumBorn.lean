import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-cutoff continuum Born self-energy for the massive-Dirac model

This Phase 4 consumer introduces the first model-specific continuum momentum-scattering Born
closure for the massive-Dirac AHE program.  It is deliberately separate from the exact finite
scalar ensemble in `Disorder/ScalarCovariance.lean`.

The clean Green operator is first paired under momentum inversion.  The exact symmetry theorem from
`PropagatorSymmetry.lean` removes the odd `σₓ` and `σᵧ` channels.  After radial reduction, the
finite-cutoff Born kernel therefore has the form

```text
Σ_s(ε; pMax) = Σ₀,s(ε; pMax) I + Σ_z,s(ε; pMax) σ_z.
```

The radial integral keeps the `p dp` Jacobian explicit.  The continuum prefactor uses the existing
physical-momentum measure `d²p/(2πℏ)²`, so angular reduction contributes the factor `2π`.

No ultraviolet limit, zero-broadening limit, exact disorder average, SCBA closure, scattering-rate
identification, or current-vertex resummation is claimed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Pair a clean propagator with its momentum-inverted partner.  This wrapper is introduced only
now that the continuum Born consumer needs an explicit inversion-symmetric integrand. -/
noncomputable def inversionSymmetrizedPauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (1 / 2 : ℂ) •
    (pauliGreenOperator side v m px py probeEnergy broadening +
      pauliGreenOperator side v m (-px) (-py) probeEnergy broadening)

/-- Exact momentum-inversion symmetrization retains only the scalar and `σ_z` Pauli channels. -/
theorem inversionSymmetrizedPauliGreenOperator_eq_evenChannels
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    inversionSymmetrizedPauliGreenOperator side v m px py probeEnergy broadening =
      pauliGreenScalarCoefficient side v m px py probeEnergy broadening • 1 +
        pauliGreenZCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaZ := by
  unfold inversionSymmetrizedPauliGreenOperator
  rw [pauliGreenOperator_add_neg_momentum]
  module

/-- Scalar-channel radial integrand after inversion/angular reduction, including the `p dp`
Jacobian. -/
noncomputable def continuumBornRadialScalarIntegrand
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) : ℂ :=
  (p : ℂ) * pauliGreenScalarCoefficient side v m p 0 probeEnergy broadening

/-- `σ_z`-channel radial integrand after inversion/angular reduction, including the `p dp`
Jacobian. -/
noncomputable def continuumBornRadialZIntegrand
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) : ℂ :=
  (p : ℂ) * pauliGreenZCoefficient side v m p 0 probeEnergy broadening

/-- Operator-valued radial Green kernel before the continuum disorder and measure prefactors are
applied. -/
noncomputable def continuumBornRadialGreenKernel
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (p : ℂ) • inversionSymmetrizedPauliGreenOperator
    side v m p 0 probeEnergy broadening

/-- Pointwise radial kernel decomposition into the two surviving Pauli channels. -/
theorem continuumBornRadialGreenKernel_eq
    (side : SpectralSide) (v m probeEnergy broadening p : ℝ) :
    continuumBornRadialGreenKernel side v m probeEnergy broadening p =
      continuumBornRadialScalarIntegrand side v m probeEnergy broadening p • 1 +
        continuumBornRadialZIntegrand side v m probeEnergy broadening p •
          matrixOperator sigmaZ := by
  rw [continuumBornRadialGreenKernel, inversionSymmetrizedPauliGreenOperator_eq_evenChannels]
  simp [continuumBornRadialScalarIntegrand, continuumBornRadialZIntegrand, smul_add, smul_smul]

private theorem continuous_pauliGreenDenominator_radial
    (side : SpectralSide) (v m probeEnergy broadening : ℝ) :
    Continuous (fun p : ℝ =>
      pauliGreenDenominator side v m p 0 probeEnergy broadening) := by
  unfold pauliGreenDenominator energySq spectralParameter
  fun_prop

private theorem continuous_pauliGreenScalarCoefficient_radial
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (fun p : ℝ =>
      pauliGreenScalarCoefficient side v m p 0 probeEnergy broadening) := by
  have hden := continuous_pauliGreenDenominator_radial side v m probeEnergy broadening
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominator side v m p 0 probeEnergy broadening)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominator_ne_zero side v m p 0 probeEnergy broadening hbroadening)
  unfold pauliGreenScalarCoefficient
  exact hinv.mul continuous_const

private theorem continuous_pauliGreenZCoefficient_radial
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (fun p : ℝ =>
      pauliGreenZCoefficient side v m p 0 probeEnergy broadening) := by
  have hden := continuous_pauliGreenDenominator_radial side v m probeEnergy broadening
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominator side v m p 0 probeEnergy broadening)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominator_ne_zero side v m p 0 probeEnergy broadening hbroadening)
  unfold pauliGreenZCoefficient
  exact hinv.mul continuous_const

private theorem continuous_continuumBornRadialScalarIntegrand
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (continuumBornRadialScalarIntegrand side v m probeEnergy broadening) := by
  unfold continuumBornRadialScalarIntegrand
  exact (Complex.continuous_ofReal.comp continuous_id).mul
    (continuous_pauliGreenScalarCoefficient_radial
      side v m probeEnergy broadening hbroadening)

private theorem continuous_continuumBornRadialZIntegrand
    (side : SpectralSide) (v m probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    Continuous (continuumBornRadialZIntegrand side v m probeEnergy broadening) := by
  unfold continuumBornRadialZIntegrand
  exact (Complex.continuous_ofReal.comp continuous_id).mul
    (continuous_pauliGreenZCoefficient_radial
      side v m probeEnergy broadening hbroadening)

/-- Finite-cutoff radial integral of the scalar Green coefficient. -/
noncomputable def finiteCutoffContinuumBornScalarIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialScalarIntegrand side v m probeEnergy broadening p

/-- Finite-cutoff radial integral of the `σ_z` Green coefficient. -/
noncomputable def finiteCutoffContinuumBornZIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialZIntegrand side v m probeEnergy broadening p

/-- Finite-cutoff operator-valued radial Green integral before disorder/measure prefactors. -/
noncomputable def finiteCutoffContinuumBornGreenIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialGreenKernel side v m probeEnergy broadening p

/-- The finite-cutoff operator-valued radial integral has exactly the `I + σ_z` structure. -/
theorem finiteCutoffContinuumBornGreenIntegral_eq
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornGreenIntegral side v m probeEnergy broadening pMax =
      finiteCutoffContinuumBornScalarIntegral side v m probeEnergy broadening pMax • 1 +
        finiteCutoffContinuumBornZIntegral side v m probeEnergy broadening pMax •
          matrixOperator sigmaZ := by
  have hscalar :=
    (continuous_continuumBornRadialScalarIntegrand
      side v m probeEnergy broadening hbroadening).intervalIntegrable
  have hz :=
    (continuous_continuumBornRadialZIntegrand
      side v m probeEnergy broadening hbroadening).intervalIntegrable
  unfold finiteCutoffContinuumBornGreenIntegral
  have hkernel :
      (fun p : ℝ => continuumBornRadialGreenKernel side v m probeEnergy broadening p) =
        fun p : ℝ =>
          continuumBornRadialScalarIntegrand side v m probeEnergy broadening p •
              (1 : DiracHilbert →L[ℂ] DiracHilbert) +
            continuumBornRadialZIntegrand side v m probeEnergy broadening p •
              matrixOperator sigmaZ := by
    funext p
    exact continuumBornRadialGreenKernel_eq side v m probeEnergy broadening p
  rw [hkernel]
  rw [intervalIntegral.integral_add (hscalar.smul_const _) (hz.smul_const _)]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rfl

/-- Angular factor multiplying the existing physical-momentum measure after radial reduction:
`2π /(2πℏ)²`. -/
def continuumBornAngularMeasurePrefactor (hbar : ℝ) : ℝ :=
  2 * Real.pi * momentumMeasurePrefactor hbar

/-- Finite-cutoff continuum scalar-disorder Born self-energy.

`disorderStrength` is a new continuum coupling parameter.  It is intentionally not identified with
the finite-ensemble `secondMomentStrength` from `ScalarCovariance.lean`. -/
noncomputable def finiteCutoffContinuumBornSelfEnergy
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) •
    finiteCutoffContinuumBornGreenIntegral side v m probeEnergy broadening pMax

/-- The model-specific finite-cutoff continuum Born self-energy contains only scalar and `σ_z`
Pauli channels. -/
theorem finiteCutoffContinuumBornSelfEnergy_eq
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornSelfEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax =
      (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegral
            side v m probeEnergy broadening pMax) • 1 +
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegral
            side v m probeEnergy broadening pMax) • matrixOperator sigmaZ := by
  rw [finiteCutoffContinuumBornSelfEnergy,
    finiteCutoffContinuumBornGreenIntegral_eq
      side v m probeEnergy broadening pMax hbroadening]
  simp [smul_add, smul_smul]

/-- Retarded finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornRetardedSelfEnergy
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornSelfEnergy .retarded
    v m probeEnergy broadening disorderStrength hbar pMax

/-- Advanced finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornAdvancedSelfEnergy
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornSelfEnergy .advanced
    v m probeEnergy broadening disorderStrength hbar pMax

end

end AnomalousHall.MassiveDirac
