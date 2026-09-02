import LeanCondensedMatter.Transport.Models.MassiveDirac.PropagatorSymmetry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-cutoff continuum Born self-energy for the massive-Dirac model

The analytic core is written at an arbitrary signed regulator `γ`. The clean Green operator is paired
under momentum inversion using the exact symmetry API from `PropagatorSymmetry.lean`; after radial
reduction the finite-cutoff Born kernel has only scalar and `σ_z` Pauli channels. Physical spectral
sides specialize through `γ = side.sign * η`.

The radial integral keeps the `p dp` Jacobian explicit. The continuum prefactor uses the existing
physical-momentum measure `d²p/(2πℏ)²`, so angular reduction contributes the factor `2π`.

No ultraviolet limit, zero-broadening limit, exact disorder average, SCBA closure, scattering-rate
identification, or current-vertex resummation is claimed here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Scalar-channel radial Born integrand at an arbitrary signed regulator, including the `p dp`
Jacobian. -/
noncomputable def continuumBornRadialScalarIntegrandOfRegulator
    (v m probeEnergy regulator p : ℝ) : ℂ :=
  (p : ℂ) * pauliGreenScalarCoefficientOfRegulator v m p 0 probeEnergy regulator

/-- `σ_z`-channel radial Born integrand at an arbitrary signed regulator, including the `p dp`
Jacobian. -/
noncomputable def continuumBornRadialZIntegrandOfRegulator
    (v m probeEnergy regulator p : ℝ) : ℂ :=
  (p : ℂ) * pauliGreenZCoefficientOfRegulator v m p 0 probeEnergy regulator

/-- Operator-valued radial Green kernel at an arbitrary signed regulator before continuum disorder
and measure prefactors are applied. -/
noncomputable def continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  (p : ℂ) • inversionSymmetrizedPauliGreenOperatorOfRegulator
    v m p 0 probeEnergy regulator

/-- Pointwise arbitrary-regulator radial kernel decomposition into the two surviving Pauli channels. -/
theorem continuumBornRadialGreenKernelOfRegulator_eq
    (v m probeEnergy regulator p : ℝ) :
    continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p =
      continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p • 1 +
        continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p •
          matrixOperator sigmaZ := by
  rw [continuumBornRadialGreenKernelOfRegulator,
    inversionSymmetrizedPauliGreenOperatorOfRegulator_eq_evenChannels]
  simp [continuumBornRadialScalarIntegrandOfRegulator,
    continuumBornRadialZIntegrandOfRegulator, smul_add, smul_smul]

private theorem star_continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) (hregulator : regulator ≠ 0) :
    star (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p) =
      continuumBornRadialGreenKernelOfRegulator v m probeEnergy (-regulator) p := by
  unfold continuumBornRadialGreenKernelOfRegulator
    inversionSymmetrizedPauliGreenOperatorOfRegulator
  simp [star_pauliGreenOperatorOfRegulator, hregulator]

private theorem continuous_pauliGreenDenominatorOfRegulator_radial
    (v m probeEnergy regulator : ℝ) :
    Continuous (fun p : ℝ =>
      pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator) := by
  unfold pauliGreenDenominatorOfRegulator energySq spectralParameterOfRegulator
  fun_prop

private theorem continuous_pauliGreenScalarCoefficientOfRegulator_radial
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (fun p : ℝ =>
      pauliGreenScalarCoefficientOfRegulator v m p 0 probeEnergy regulator) := by
  have hden := continuous_pauliGreenDenominatorOfRegulator_radial
    v m probeEnergy regulator
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominatorOfRegulator_ne_zero
        v m p 0 probeEnergy regulator hregulator)
  unfold pauliGreenScalarCoefficientOfRegulator
  exact hinv.mul continuous_const

private theorem continuous_pauliGreenZCoefficientOfRegulator_radial
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (fun p : ℝ =>
      pauliGreenZCoefficientOfRegulator v m p 0 probeEnergy regulator) := by
  have hden := continuous_pauliGreenDenominatorOfRegulator_radial
    v m probeEnergy regulator
  have hinv : Continuous (fun p : ℝ =>
      (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹) :=
    hden.inv₀ (fun p =>
      pauliGreenDenominatorOfRegulator_ne_zero
        v m p 0 probeEnergy regulator hregulator)
  unfold pauliGreenZCoefficientOfRegulator
  exact hinv.mul continuous_const

private theorem continuous_continuumBornRadialScalarIntegrandOfRegulator
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialScalarIntegrandOfRegulator
      v m probeEnergy regulator) := by
  unfold continuumBornRadialScalarIntegrandOfRegulator
  exact (Complex.continuous_ofReal.comp continuous_id).mul
    (continuous_pauliGreenScalarCoefficientOfRegulator_radial
      v m probeEnergy regulator hregulator)

private theorem continuous_continuumBornRadialZIntegrandOfRegulator
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator) := by
  unfold continuumBornRadialZIntegrandOfRegulator
  exact (Complex.continuous_ofReal.comp continuous_id).mul
    (continuous_pauliGreenZCoefficientOfRegulator_radial
      v m probeEnergy regulator hregulator)

private theorem continuous_continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator) := by
  rw [show continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator =
      fun p : ℝ =>
        continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p •
            matrixOperator sigmaZ by
    funext p
    exact continuumBornRadialGreenKernelOfRegulator_eq v m probeEnergy regulator p]
  exact
    ((continuous_continuumBornRadialScalarIntegrandOfRegulator
      v m probeEnergy regulator hregulator).smul continuous_const).add
      ((continuous_continuumBornRadialZIntegrandOfRegulator
        v m probeEnergy regulator hregulator).smul continuous_const)

/-- Finite-cutoff radial integral of the scalar Green coefficient at an arbitrary signed
regulator. -/
noncomputable def finiteCutoffContinuumBornScalarIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p

/-- Finite-cutoff radial integral of the `σ_z` Green coefficient at an arbitrary signed
regulator. -/
noncomputable def finiteCutoffContinuumBornZIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p

/-- Finite-cutoff operator-valued radial Green integral at an arbitrary signed regulator before
continuum disorder and measure prefactors. -/
noncomputable def finiteCutoffContinuumBornGreenIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p

/-- Physical-side scalar radial integral. -/
noncomputable def finiteCutoffContinuumBornScalarIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornScalarIntegralOfRegulator
    v m probeEnergy (side.sign * broadening) pMax

/-- Physical-side `σ_z` radial integral. -/
noncomputable def finiteCutoffContinuumBornZIntegral
    (side : SpectralSide) (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornZIntegralOfRegulator
    v m probeEnergy (side.sign * broadening) pMax

/-- The arbitrary-regulator finite-cutoff operator integral has exactly the `I + σ_z` structure. -/
theorem finiteCutoffContinuumBornGreenIntegralOfRegulator_eq
    (v m probeEnergy regulator pMax : ℝ) (hregulator : regulator ≠ 0) :
    finiteCutoffContinuumBornGreenIntegralOfRegulator v m probeEnergy regulator pMax =
      finiteCutoffContinuumBornScalarIntegralOfRegulator v m probeEnergy regulator pMax • 1 +
        finiteCutoffContinuumBornZIntegralOfRegulator v m probeEnergy regulator pMax •
          matrixOperator sigmaZ := by
  have hscalarOp :
      IntervalIntegrable
        (fun p : ℝ =>
          continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p •
            (1 : DiracHilbert →L[ℂ] DiracHilbert))
        volume 0 pMax :=
    ((continuous_continuumBornRadialScalarIntegrandOfRegulator
      v m probeEnergy regulator hregulator).smul continuous_const).intervalIntegrable 0 pMax
  have hzOp :
      IntervalIntegrable
        (fun p : ℝ =>
          continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p •
            matrixOperator sigmaZ)
        volume 0 pMax :=
    ((continuous_continuumBornRadialZIntegrandOfRegulator
      v m probeEnergy regulator hregulator).smul continuous_const).intervalIntegrable 0 pMax
  unfold finiteCutoffContinuumBornGreenIntegralOfRegulator
  have hkernel :
      (fun p : ℝ => continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p) =
        fun p : ℝ =>
          continuumBornRadialScalarIntegrandOfRegulator v m probeEnergy regulator p •
              (1 : DiracHilbert →L[ℂ] DiracHilbert) +
            continuumBornRadialZIntegrandOfRegulator v m probeEnergy regulator p •
              matrixOperator sigmaZ := by
    funext p
    exact continuumBornRadialGreenKernelOfRegulator_eq v m probeEnergy regulator p
  rw [hkernel]
  rw [intervalIntegral.integral_add hscalarOp hzOp]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rfl

private theorem star_finiteCutoffContinuumBornGreenIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) (hregulator : regulator ≠ 0) :
    star (finiteCutoffContinuumBornGreenIntegralOfRegulator
      v m probeEnergy regulator pMax) =
      finiteCutoffContinuumBornGreenIntegralOfRegulator
        v m probeEnergy (-regulator) pMax := by
  let adjointL :
      (DiracHilbert →L[ℂ] DiracHilbert) →L[ℝ]
        (DiracHilbert →L[ℂ] DiracHilbert) :=
    (starL' ℝ).toContinuousLinearMap
  have hint :
      IntervalIntegrable
        (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator)
        volume 0 pMax :=
    (continuous_continuumBornRadialGreenKernelOfRegulator
      v m probeEnergy regulator hregulator).intervalIntegrable 0 pMax
  unfold finiteCutoffContinuumBornGreenIntegralOfRegulator
  calc
    star (∫ p in (0 : ℝ)..pMax,
        continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p) =
        ∫ p in (0 : ℝ)..pMax,
          star (continuumBornRadialGreenKernelOfRegulator
            v m probeEnergy regulator p) := by
      symm
      simpa [adjointL] using
        (adjointL.intervalIntegral_comp_comm hint)
    _ = ∫ p in (0 : ℝ)..pMax,
        continuumBornRadialGreenKernelOfRegulator v m probeEnergy (-regulator) p := by
      apply intervalIntegral.integral_congr
      intro p hp
      exact star_continuumBornRadialGreenKernelOfRegulator
        v m probeEnergy regulator p hregulator

/-- Angular factor multiplying the existing physical-momentum measure after radial reduction:
`2π /(2πℏ)²`. -/
def continuumBornAngularMeasurePrefactor (hbar : ℝ) : ℝ :=
  2 * Real.pi * momentumMeasurePrefactor hbar

/-- Finite-cutoff continuum scalar-disorder Born self-energy at an arbitrary signed regulator.

`disorderStrength` is a continuum coupling parameter. It is intentionally not identified with the
finite-ensemble `secondMomentStrength` from `ScalarCovariance.lean`. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyOfRegulator
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) •
    finiteCutoffContinuumBornGreenIntegralOfRegulator v m probeEnergy regulator pMax

/-- Physical-side specialization of the finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornSelfEnergy
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornSelfEnergyOfRegulator
    v m probeEnergy (side.sign * broadening) disorderStrength hbar pMax

/-- The arbitrary-regulator continuum Born self-energy contains only scalar and `σ_z` channels. -/
theorem finiteCutoffContinuumBornSelfEnergyOfRegulator_eq
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ)
    (hregulator : regulator ≠ 0) :
    finiteCutoffContinuumBornSelfEnergyOfRegulator
        v m probeEnergy regulator disorderStrength hbar pMax =
      (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornScalarIntegralOfRegulator
            v m probeEnergy regulator pMax) • 1 +
        (((disorderStrength * continuumBornAngularMeasurePrefactor hbar : ℝ) : ℂ) *
          finiteCutoffContinuumBornZIntegralOfRegulator
            v m probeEnergy regulator pMax) • matrixOperator sigmaZ := by
  rw [finiteCutoffContinuumBornSelfEnergyOfRegulator,
    finiteCutoffContinuumBornGreenIntegralOfRegulator_eq
      v m probeEnergy regulator pMax hregulator]
  simp [smul_add, smul_smul]

/-- Physical-side channel decomposition, retained because it is consumed by downstream transport
calculations. -/
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
  simpa [finiteCutoffContinuumBornSelfEnergy, finiteCutoffContinuumBornScalarIntegral,
    finiteCutoffContinuumBornZIntegral] using
    finiteCutoffContinuumBornSelfEnergyOfRegulator_eq
      v m probeEnergy (side.sign * broadening) disorderStrength hbar pMax
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

/-- Adjointing the arbitrary-regulator continuum Born self-energy reverses the regulator. -/
theorem star_finiteCutoffContinuumBornSelfEnergyOfRegulator
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ)
    (hregulator : regulator ≠ 0) :
    star (finiteCutoffContinuumBornSelfEnergyOfRegulator
      v m probeEnergy regulator disorderStrength hbar pMax) =
      finiteCutoffContinuumBornSelfEnergyOfRegulator
        v m probeEnergy (-regulator) disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornSelfEnergyOfRegulator
  rw [star_smul, star_finiteCutoffContinuumBornGreenIntegralOfRegulator
    v m probeEnergy regulator pMax hregulator]
  simp

/-- Physical-side adjunction, retained for downstream Born-Dyson consumers. -/
theorem star_finiteCutoffContinuumBornSelfEnergy
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    star (finiteCutoffContinuumBornSelfEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornSelfEnergy
        side.opposite v m probeEnergy broadening disorderStrength hbar pMax := by
  simpa [finiteCutoffContinuumBornSelfEnergy, SpectralSide.sign_opposite,
    neg_mul] using
    star_finiteCutoffContinuumBornSelfEnergyOfRegulator
      v m probeEnergy (side.sign * broadening) disorderStrength hbar pMax
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

end

end AnomalousHall.MassiveDirac
