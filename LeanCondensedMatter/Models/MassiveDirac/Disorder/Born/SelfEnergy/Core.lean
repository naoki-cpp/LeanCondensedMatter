import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Propagator.AngularReduction
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite-cutoff continuum Born self-energy core

This module owns the finite-cutoff continuum Born self-energy and its channelized radial decomposition.
The analytic core is written at an
arbitrary signed regulator `γ`; physical spectral sides specialize through the canonical
`side.regulator η` boundary.

The radial integral keeps the `p dp` Jacobian explicit, and the continuum prefactor keeps the
physical-momentum measure `d²p/(2πℏ)²`. The two surviving isotropic Pauli channels are represented
by one indexed API. The independent explicit angular-integral provenance is developed in
`SelfEnergy.PolarProvenance`; their common denominator factorization is developed in
`SelfEnergy.DenominatorIntegral`.

No ultraviolet limit, zero-broadening limit, exact disorder average, SCBA closure, scattering-rate
identification, or current-vertex resummation is claimed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- The two isotropic Pauli channels that survive angular reduction of the scalar-disorder Born
self-energy: the identity/scalar channel and the `σ_z` channel. -/
inductive BornSelfEnergyChannel where
  | scalar
  | z
  deriving DecidableEq

/-- Multiplicative numerator carried by a Born self-energy channel at arbitrary signed regulator. -/
def bornSelfEnergyChannelWeightOfRegulator
    (channel : BornSelfEnergyChannel) (m probeEnergy regulator : ℝ) : ℂ :=
  match channel with
  | .scalar => spectralParameterOfRegulator probeEnergy regulator
  | .z => (m : ℂ)

/-- Physical-side specialization of the Born self-energy channel numerator. -/
def bornSelfEnergyChannelWeight
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (m probeEnergy broadening : ℝ) : ℂ :=
  bornSelfEnergyChannelWeightOfRegulator
    channel m probeEnergy (side.regulator broadening)

/-- Radial Born integrand for either surviving isotropic self-energy channel at an arbitrary signed
regulator, including the `p dp` Jacobian. -/
noncomputable def continuumBornRadialIntegrandOfRegulator
    (channel : BornSelfEnergyChannel)
    (v m probeEnergy regulator p : ℝ) : ℂ :=
  match channel with
  | .scalar =>
      (p : ℂ) * pauliGreenScalarCoefficientOfRegulator v m p 0 probeEnergy regulator
  | .z =>
      (p : ℂ) * pauliGreenPauliCoefficientOfRegulator .z v m p 0 probeEnergy regulator

/-- Operator-valued radial Green kernel at an arbitrary signed regulator before continuum disorder
and measure prefactors are applied. -/
noncomputable def continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  (p : ℂ) • inversionSymmetrizedPauliGreenOperatorOfRegulator
    v m p 0 probeEnergy regulator

/-- Pointwise arbitrary-regulator radial kernel decomposition into the two surviving Pauli channels. -/
private theorem continuumBornRadialGreenKernelOfRegulator_eq
    (v m probeEnergy regulator p : ℝ) :
    continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p =
      continuumBornRadialIntegrandOfRegulator .scalar
          v m probeEnergy regulator p • 1 +
        continuumBornRadialIntegrandOfRegulator .z
          v m probeEnergy regulator p • matrixOperator sigmaZ := by
  rw [continuumBornRadialGreenKernelOfRegulator,
    inversionSymmetrizedPauliGreenOperatorOfRegulator_eq_evenChannels]
  simp [continuumBornRadialIntegrandOfRegulator, smul_add, smul_smul]

private theorem star_continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator p : ℝ) (hregulator : regulator ≠ 0) :
    star (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p) =
      continuumBornRadialGreenKernelOfRegulator v m probeEnergy (-regulator) p := by
  unfold continuumBornRadialGreenKernelOfRegulator
    inversionSymmetrizedPauliGreenOperatorOfRegulator
  simp [star_pauliGreenOperatorOfRegulator, hregulator]

/-- Every surviving Born self-energy radial channel is continuous away from zero regulator. -/
theorem continuous_continuumBornRadialIntegrandOfRegulator
    (channel : BornSelfEnergyChannel)
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialIntegrandOfRegulator
      channel v m probeEnergy regulator) := by
  have hcommon (coeff : ℂ) :
      Continuous (fun p : ℝ => (p : ℂ) *
        ((pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹ * coeff)) :=
    (Complex.continuous_ofReal.comp continuous_id).mul
      ((continuous_inv_pauliGreenDenominatorOfRegulator_radial
        v m probeEnergy regulator hregulator).mul continuous_const)
  cases channel with
  | scalar =>
      exact hcommon (spectralParameterOfRegulator probeEnergy regulator)
  | z =>
      exact hcommon (m : ℂ)

/-- The operator-valued radial Born Green kernel is continuous away from zero regulator. -/
theorem continuous_continuumBornRadialGreenKernelOfRegulator
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator) := by
  rw [show continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator =
      fun p : ℝ =>
        continuumBornRadialIntegrandOfRegulator .scalar v m probeEnergy regulator p •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) +
          continuumBornRadialIntegrandOfRegulator .z v m probeEnergy regulator p •
            matrixOperator sigmaZ by
    funext p
    exact continuumBornRadialGreenKernelOfRegulator_eq v m probeEnergy regulator p]
  exact
    ((continuous_continuumBornRadialIntegrandOfRegulator
      .scalar v m probeEnergy regulator hregulator).smul continuous_const).add
      ((continuous_continuumBornRadialIntegrandOfRegulator
        .z v m probeEnergy regulator hregulator).smul continuous_const)

/-- Finite-cutoff radial integral of either surviving Born self-energy channel at an arbitrary
signed regulator. -/
noncomputable def finiteCutoffContinuumBornIntegralOfRegulator
    (channel : BornSelfEnergyChannel)
    (v m probeEnergy regulator pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialIntegrandOfRegulator channel v m probeEnergy regulator p

/-- Finite-cutoff operator-valued radial Green integral at an arbitrary signed regulator before
continuum disorder and measure prefactors. -/
noncomputable def finiteCutoffContinuumBornGreenIntegralOfRegulator
    (v m probeEnergy regulator pMax : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p

/-- Physical-side finite-cutoff radial integral of either surviving Born self-energy channel. -/
noncomputable def finiteCutoffContinuumBornIntegral
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornIntegralOfRegulator
    channel v m probeEnergy (side.regulator broadening) pMax

/-- The arbitrary-regulator finite-cutoff operator integral has exactly the `I + σ_z` structure. -/
theorem finiteCutoffContinuumBornGreenIntegralOfRegulator_eq
    (v m probeEnergy regulator pMax : ℝ) (hregulator : regulator ≠ 0) :
    finiteCutoffContinuumBornGreenIntegralOfRegulator v m probeEnergy regulator pMax =
      finiteCutoffContinuumBornIntegralOfRegulator .scalar
          v m probeEnergy regulator pMax • 1 +
        finiteCutoffContinuumBornIntegralOfRegulator .z
          v m probeEnergy regulator pMax • matrixOperator sigmaZ := by
  have hchannelOp (channel : BornSelfEnergyChannel)
      (op : DiracHilbert →L[ℂ] DiracHilbert) :
      IntervalIntegrable
        (fun p : ℝ => continuumBornRadialIntegrandOfRegulator
          channel v m probeEnergy regulator p • op) volume 0 pMax :=
    ((continuous_continuumBornRadialIntegrandOfRegulator
      channel v m probeEnergy regulator hregulator).smul continuous_const).intervalIntegrable
        0 pMax
  unfold finiteCutoffContinuumBornGreenIntegralOfRegulator
  have hkernel :
      (fun p : ℝ => continuumBornRadialGreenKernelOfRegulator v m probeEnergy regulator p) =
        fun p : ℝ =>
          continuumBornRadialIntegrandOfRegulator .scalar v m probeEnergy regulator p •
              (1 : DiracHilbert →L[ℂ] DiracHilbert) +
            continuumBornRadialIntegrandOfRegulator .z v m probeEnergy regulator p •
              matrixOperator sigmaZ := by
    funext p
    exact continuumBornRadialGreenKernelOfRegulator_eq v m probeEnergy regulator p
  rw [hkernel]
  rw [intervalIntegral.integral_add (hchannelOp .scalar 1)
    (hchannelOp .z (matrixOperator sigmaZ))]
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

/-- Finite-cutoff coefficient of either surviving Born self-energy channel at arbitrary signed
regulator. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator
    (channel : BornSelfEnergyChannel)
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) : ℂ :=
  (((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornIntegralOfRegulator
      channel v m probeEnergy regulator pMax)

/-- Physical-side finite-cutoff coefficient of either surviving Born self-energy channel. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyCoefficient
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator
    channel v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax

@[simp] theorem finiteCutoffContinuumBornSelfEnergyCoefficient_zero_disorder
    (channel : BornSelfEnergyChannel) (side : SpectralSide)
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornSelfEnergyCoefficient
      channel side v m probeEnergy broadening 0 hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornSelfEnergyCoefficient,
    finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator]

/-- Finite-cutoff continuum scalar-disorder Born self-energy at an arbitrary signed regulator.

`disorderStrength` is a continuum coupling parameter. It is intentionally not identified with the
finite-ensemble `secondMomentStrength` from `ScalarCovariance.lean`. -/
noncomputable def finiteCutoffContinuumBornSelfEnergyOfRegulator
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ((disorderStrength * fullAngleMomentumMeasurePrefactor hbar : ℝ) : ℂ) •
    finiteCutoffContinuumBornGreenIntegralOfRegulator v m probeEnergy regulator pMax

/-- Physical-side specialization of the finite-cutoff continuum Born self-energy. -/
noncomputable def finiteCutoffContinuumBornSelfEnergy
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  finiteCutoffContinuumBornSelfEnergyOfRegulator
    v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax

/-- The arbitrary-regulator continuum Born self-energy contains only scalar and `σ_z` channels. -/
private theorem finiteCutoffContinuumBornSelfEnergyOfRegulator_eq
    (v m probeEnergy regulator disorderStrength hbar pMax : ℝ)
    (hregulator : regulator ≠ 0) :
    finiteCutoffContinuumBornSelfEnergyOfRegulator
        v m probeEnergy regulator disorderStrength hbar pMax =
      finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator .scalar
          v m probeEnergy regulator disorderStrength hbar pMax • 1 +
        finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator .z
          v m probeEnergy regulator disorderStrength hbar pMax • matrixOperator sigmaZ := by
  rw [finiteCutoffContinuumBornSelfEnergyOfRegulator,
    finiteCutoffContinuumBornGreenIntegralOfRegulator_eq
      v m probeEnergy regulator pMax hregulator]
  simp [finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator, smul_add, smul_smul]

/-- Physical-side channel decomposition, retained because it is consumed by downstream transport
calculations. -/
theorem finiteCutoffContinuumBornSelfEnergy_eq
    (side : SpectralSide) (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornSelfEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornSelfEnergyCoefficient .scalar
          side v m probeEnergy broadening disorderStrength hbar pMax • 1 +
        finiteCutoffContinuumBornSelfEnergyCoefficient .z
          side v m probeEnergy broadening disorderStrength hbar pMax • matrixOperator sigmaZ := by
  simpa [finiteCutoffContinuumBornSelfEnergy,
    finiteCutoffContinuumBornSelfEnergyCoefficient,
    finiteCutoffContinuumBornSelfEnergyCoefficientOfRegulator] using
    finiteCutoffContinuumBornSelfEnergyOfRegulator_eq
      v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax
      (side.regulator_ne_zero hbroadening)

/-- Adjointing the arbitrary-regulator continuum Born self-energy reverses the regulator. -/
private theorem star_finiteCutoffContinuumBornSelfEnergyOfRegulator
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
  simpa [finiteCutoffContinuumBornSelfEnergy] using
    star_finiteCutoffContinuumBornSelfEnergyOfRegulator
      v m probeEnergy (side.regulator broadening) disorderStrength hbar pMax
      (side.regulator_ne_zero hbroadening)

end

end QuantumTheory.Models.MassiveDirac
