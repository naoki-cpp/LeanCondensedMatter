import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalSameSide
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRadialCoefficients
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gaussian-crossed radial current Fourier harmonics

The finite-cutoff current blocks admit explicit first-harmonic and diagonal K0/K2 radial
coefficient identities. Their source/Pauli symmetries and origin selection rules are proved here,
upstream of the X/Psi trace-kernel reductions. Physical regulators remain explicit.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport

/-- The four non-diagonal first-harmonic channels of the regulated Gaussian-crossed
radial current are exact source-resolved scalar momentum integrals. The source-x and
source-y Pauli-scalar and Pauli-z components all use the same Fourier K1 kernel,
with distinct spectral coefficient combinations and signs.

These finite-cutoff identities reuse the physical Fourier momentum measure and do
not evaluate the radial integrals or remove the regulators. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let aA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let aR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        0 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((aR p * bA p + aA p * bR p) * factor))) ∧
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((-Complex.I * (bR p * dA p - bA p * dR p)) * factor))) ∧
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((bR p * dA p + bA p * dR p) * factor))) ∧
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((-Complex.I * (aA p * bR p - aR p * bA p)) * factor))) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
      0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    apply congrArg (fun w : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * w)
    apply intervalIntegral.integral_congr
    intro p _
    rfl
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
      1 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    apply congrArg (fun w : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * w)
    apply intervalIntegral.integral_congr
    intro p _
    rfl
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    apply congrArg (fun w : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * w)
    apply intervalIntegral.integral_congr
    intro p _
    rfl
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    apply congrArg (fun w : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * w)
    apply intervalIntegral.integral_congr
    intro p _
    rfl

/-- The zeroth-radius crossed-current block has neither a Pauli-scalar nor a
longitudinal Pauli-z component. Both channels carry the first angular Fourier
harmonic, which vanishes at the origin before momentum integration.

This is an exact finite-broadening, finite-cutoff selection rule; it does not
require a real-space regulator limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_origin_scalar_and_z_eq_zero
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
      source v m probeEnergy broadening disorderStrength hbar pMax 0 = 0) ∧
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .z source v m probeEnergy broadening disorderStrength hbar pMax 0 = 0) := by
  constructor
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
      source v m probeEnergy broadening disorderStrength hbar pMax 0
      hbroadening hdisorder hpMax]
    simp [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel]
  · rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .z source v m probeEnergy broadening disorderStrength hbar pMax 0
      hbroadening hdisorder hpMax]
    simp [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel]

/-- The pointwise transverse antisymmetry survives radial momentum integration in the
physical finite-broadening finite-cutoff regime. It reduces the number of independent
crossed-current coefficients needed for the `X` and `Psi` trace evaluations. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_y_zero_eq_neg_x_one
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius =
      -finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .x 1 v m probeEnergy broadening disorderStrength hbar pMax radius := by
  rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .x 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax]
  simp_rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel_y_zero_eq_neg_x_one]
  simp

/-- Finite-cutoff diagonal crossed-current Pauli coefficients split after radial momentum
integration into independent zeroth- and second-harmonic integrals. No momentum measure is
added beyond that already present in the real-space Fourier current blocks.

This does not evaluate the integrals or remove the regulators. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_harmonics
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let aA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let aR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    (jxx + jyy =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) *
              ((aA p * aR p - dA p * dR p) * factor))) ∧
    (jxx - jyy =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) *
            (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              (bA p * bR p * factor))) := by
  have hkernel (axis : PauliAxis) (source : Fin 2) :
      IntervalIntegrable
        (fun p : ℝ =>
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            axis source v m probeEnergy broadening disorderStrength hbar pMax radius p)
        volume 0 pMax := by
    have hentry (i j : Fin 2) :
        Continuous (fun p : ℝ =>
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j) :=
      continuous_finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax i j
    have hcoeff :
        Continuous (fun p : ℝ =>
          InternalSpace.pauliVectorCoefficient
            (fun i j =>
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                source v m probeEnergy broadening disorderStrength hbar pMax radius p i j) axis) := by
      cases axis <;>
        simp only [InternalSpace.pauliVectorCoefficient] <;> fun_prop
    have heq :
        (fun p : ℝ => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
          axis source v m probeEnergy broadening disorderStrength hbar pMax radius p) =
        (fun p : ℝ => InternalSpace.pauliVectorCoefficient
          (fun i j => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j) axis) := by
      funext p
      exact
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
          axis source v m probeEnergy broadening disorderStrength hbar pMax radius p).symm
    rw [heq]
    exact hcoeff.intervalIntegrable 0 pMax
  have hxx := hkernel .x 0
  have hyy := hkernel .y 1
  dsimp only
  constructor
  · rw [
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
        .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    calc
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (∫ p in (0 : ℝ)..pMax, finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius p) +
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (∫ p in (0 : ℝ)..pMax, finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius p) =
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius p +
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius p := by
          rw [intervalIntegral.integral_add hxx hyy]
          ring
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            2 * (p : ℂ) *
              (polarFourierZerothAngularKernel (p * radius / hbar) *
                ((finiteCutoffContinuumBornDysonScalarCoefficient
                    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
                   finiteCutoffContinuumBornDysonScalarCoefficient
                    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax -
                   finiteCutoffContinuumBornDysonPauliCoefficient .z
                    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
                   finiteCutoffContinuumBornDysonPauliCoefficient .z
                    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax) *
                  finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor v m probeEnergy broadening disorderStrength hbar pMax)) := by
          apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
          apply intervalIntegral.integral_congr
          intro p _
          exact
            (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel_diagonal_harmonics
              v m probeEnergy broadening disorderStrength hbar pMax radius p).1
  · rw [
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
        .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax]
    calc
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (∫ p in (0 : ℝ)..pMax, finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius p) -
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (∫ p in (0 : ℝ)..pMax, finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius p) =
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius p -
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius p := by
          rw [intervalIntegral.integral_sub hxx hyy]
          ring
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            2 * (p : ℂ) *
              (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                (finiteCutoffContinuumBornDysonPauliCoefficient .x
                    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
                   finiteCutoffContinuumBornDysonPauliCoefficient .x
                    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
                   finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor v m probeEnergy broadening disorderStrength hbar pMax)) := by
          apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
          apply intervalIntegral.integral_congr
          intro p _
          exact
            (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel_diagonal_harmonics
              v m probeEnergy broadening disorderStrength hbar pMax radius p).2

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
  have hden (side : SpectralSide) (p : ℝ) :
      massiveDiracRadialDenominator v p
          (finiteCutoffContinuumBornEffectiveEnergy
            side v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornEffectiveMass
            side v m probeEnergy broadening disorderStrength hbar pMax) =
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold massiveDiracRadialDenominator finiteCutoffContinuumBornDysonDenominator
    push_cast
    ring
  have hgap (p : ℝ) :
      (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ =
        (finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
        (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
    have hR : massiveDiracRadialDenominator v p energyR massR ≠ 0 := by
      change massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          .retarded v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornEffectiveMass
          .retarded v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0
      rw [hden]
      exact finiteCutoffContinuumBornDysonDenominator_ne_zero
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax
    have hA : massiveDiracRadialDenominator v p energyA massA ≠ 0 := by
      change massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          .advanced v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornEffectiveMass
          .advanced v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0
      rw [hden]
      exact finiteCutoffContinuumBornDysonDenominator_ne_zero
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax
    have hspectral :=
      massiveDiracRadialDenominator_inv_product_mul_center_gap
        v p energyR massR energyA massA hR hA
    dsimp only [energyR, energyA, massR, massA] at hspectral
    simpa only [massiveDiracRetardedAdvancedRadialDenominatorProduct,
      hden, ← finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul]
      using hspectral
  dsimp only
  calc
    (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
        (∫ p in (0 : ℝ)..pMax, weight p *
          (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
            v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) =
      ∫ p in (0 : ℝ)..pMax,
        (energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)) *
          (weight p *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ = _ := by
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

/-- The two independent diagonal Gaussian-crossed current harmonics have a
single finite-broadening RA Dyson denominator. Their K0 numerator is the
effective-energy product minus the effective-mass product, while the K2
numerator is the squared in-plane Dirac momentum. The Fourier momentum
measure and disorder/current factor are unchanged. No denominator is
assumed nonzero and no regulator limit is taken. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_ra_denominator_harmonics
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let energyA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let energyR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let massA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let massR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let denominator := fun p : ℝ =>
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    (jxx + jyy =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) *
              ((denominator p)⁻¹ * (energyA * energyR - massA * massR) * factor))) ∧
    (jxx - jyy =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) *
            (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              ((denominator p)⁻¹ * (((v * p : ℝ) : ℂ) ^ 2) * factor))) := by
  have h :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at h ⊢
  constructor
  · rw [h.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [finiteCutoffContinuumBornDysonRadial_ra_scalar_sub_z_product_eq]
  · rw [h.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [finiteCutoffContinuumBornDysonRadial_ra_x_product_eq]

/-- The two physical diagonal crossed-current harmonics, after multiplication
by the finite-regulator RA spectral-center gap, become differences of
single-side radial Dyson resolvent moments. The K0 and K2 weights retain
their independent spectral numerator, current factor, and one momentum
measure each. No division by the center gap or regulator limit is used. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_spectral_difference
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let energyR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let energyA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let massR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let massA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    let k0Weight := fun p : ℝ =>
      2 * (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
        ((energyA * energyR - massA * massR) * factor)
    let k2Weight := fun p : ℝ =>
      2 * (p : ℂ) * polarFourierSecondCosineAngularKernel (p * radius / hbar) *
        ((((v * p : ℝ) : ℂ) ^ 2) * factor)
    (gap * (jxx + jyy) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          k0Weight p *
            ((finiteCutoffContinuumBornDysonDenominator
                .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
              (finiteCutoffContinuumBornDysonDenominator
                .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)) ∧
    (gap * (jxx - jyy) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          k2Weight p *
            ((finiteCutoffContinuumBornDysonDenominator
                .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
              (finiteCutoffContinuumBornDysonDenominator
                .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)) := by
  let energyR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let energyA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let massR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let massA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
  let k0Weight : ℝ → ℂ := fun p =>
    2 * (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
      ((energyA * energyR - massA * massR) * factor)
  let k2Weight : ℝ → ℂ := fun p =>
    2 * (p : ℂ) * polarFourierSecondCosineAngularKernel (p * radius / hbar) *
      ((((v * p : ℝ) : ℂ) ^ 2) * factor)
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_ra_denominator_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hk0 :=
    finiteCutoffContinuumBornDysonRadial_ra_weighted_moment_mul_center_gap
      v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax k0Weight
  have hk2 :=
    finiteCutoffContinuumBornDysonRadial_ra_weighted_moment_mul_center_gap
      v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax k2Weight
  dsimp only at hdiag hk0 hk2 ⊢
  have hweight0 :
      (∫ p in (0 : ℝ)..pMax,
        2 * (p : ℂ) *
          (polarFourierZerothAngularKernel (p * radius / hbar) *
            ((finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
                (energyA * energyR - massA * massR) * factor))) =
        ∫ p in (0 : ℝ)..pMax,
          k0Weight p *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only [k0Weight]
    ring
  have hweight2 :
      (∫ p in (0 : ℝ)..pMax,
        2 * (p : ℂ) *
          (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            ((finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
                (((v * p : ℝ) : ℂ) ^ 2) * factor))) =
        ∫ p in (0 : ℝ)..pMax,
          k2Weight p *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only [k2Weight]
    ring
  constructor
  · calc
      gap * (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
              .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius +
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
              .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (gap * (∫ p in (0 : ℝ)..pMax,
            2 * (p : ℂ) *
              (polarFourierZerothAngularKernel (p * radius / hbar) *
                ((finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
                  v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
                    (energyA * energyR - massA * massR) * factor)))) := by
          rw [hdiag.1]
          ring
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (gap * (∫ p in (0 : ℝ)..pMax, k0Weight p *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹)) := by
          rw [hweight0]
      _ = _ := by rw [hk0]
  · calc
      gap * (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
              .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
              .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius) =
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (gap * (∫ p in (0 : ℝ)..pMax,
            2 * (p : ℂ) *
              (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                ((finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
                  v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
                    (((v * p : ℝ) : ℂ) ^ 2) * factor)))) := by
          rw [hdiag.2]
          ring
      _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          (gap * (∫ p in (0 : ℝ)..pMax, k2Weight p *
            (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
              v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹)) := by
          rw [hweight2]
      _ = _ := by rw [hk2]

/-- The traceless second angular Fourier harmonic vanishes at the origin.
The result follows from the canonical full-angle harmonic integration theorem. -/
/-- At zero real-space separation, rotational isotropy forces equality of the
two diagonal in-plane crossed-current Pauli coefficients. This holds before any
momentum-cutoff, broadening, or weak-disorder limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_eq
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .x 0 v m probeEnergy broadening disorderStrength hbar pMax 0 =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax 0 := by
  have h :=
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax 0
      hbroadening hdisorder hpMax).2
  dsimp only at h
  simpa [polarFourierSecondCosineAngularKernel_zero, sub_eq_zero] using h

/-- At zero real-space separation, the isotropic Gaussian-crossed current
is an exactly evaluated finite-cutoff RA radial moment. Both diagonal
Pauli coefficients agree by rotational symmetry. The original physical
Fourier measure occurs only once, and the RA spectral-center gap is
retained on the left rather than inverted. The complex logarithms use
the finite-broadening Dyson branch criterion. Neither a nonzero-radius
K0/K2 moment nor a complete X/Psi Hall diagram is evaluated here. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_mul_center_gap_eq_log
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
    let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let logDiff :=
      (Complex.log (finiteCutoffContinuumBornDysonDenominator
          .retarded v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
        Complex.log (finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) -
      (Complex.log (finiteCutoffContinuumBornDysonDenominator
          .advanced v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
        Complex.log (finiteCutoffContinuumBornDysonDenominator
          .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax))
    let value := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      (((2 * Real.pi : ℝ) : ℂ)) *
      ((energyA * energyR - massA * massR) * factor) *
      (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff)
    (gap *
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax 0 = value) ∧
      (gap *
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax 0 = value) := by
  let energyR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let energyA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let massR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let massA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let logDiff :=
    (Complex.log (finiteCutoffContinuumBornDysonDenominator
        .retarded v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
      Complex.log (finiteCutoffContinuumBornDysonDenominator
        .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) -
    (Complex.log (finiteCutoffContinuumBornDysonDenominator
        .advanced v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
      Complex.log (finiteCutoffContinuumBornDysonDenominator
        .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax))
  let measure := (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
  let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
    .x 0 v m probeEnergy broadening disorderStrength hbar pMax 0
  let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
    .y 1 v m probeEnergy broadening disorderStrength hbar pMax 0
  let denominator := fun p : ℝ =>
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
      v m p probeEnergy broadening disorderStrength hbar pMax
  have hdiag :=
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_ra_denominator_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax 0
      hbroadening hdisorder hpMax).1
  have hsymm :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_eq
      v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hlog :=
    finiteCutoffContinuumBornDysonRadial_ra_pole_moment_mul_center_gap_eq_log
      v m probeEnergy broadening disorderStrength hbar pMax
      hvelocity hbroadening hdisorder hpMax hcenterR hcenterA
  dsimp only at hdiag hlog hsymm ⊢
  change jxx + jyy = measure *
      (∫ p in (0 : ℝ)..pMax, 2 * (p : ℂ) *
        (polarFourierZerothAngularKernel (p * 0 / hbar) *
          ((denominator p)⁻¹ * (energyA * energyR - massA * massR) * factor))) at hdiag
  change jxx = jyy at hsymm
  change gap * (∫ p in (0 : ℝ)..pMax, (p : ℂ) * (denominator p)⁻¹) =
    -(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff at hlog
  have hrad :
      (∫ p in (0 : ℝ)..pMax, 2 * (p : ℂ) *
        (polarFourierZerothAngularKernel (p * 0 / hbar) *
          ((denominator p)⁻¹ * (energyA * energyR - massA * massR) * factor))) =
      (2 * (((2 * Real.pi : ℝ) : ℂ)) *
        ((energyA * energyR - massA * massR) * factor)) *
        (∫ p in (0 : ℝ)..pMax, (p : ℂ) * (denominator p)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro p _
    simp only [mul_zero, zero_div, polarFourierZerothAngularKernel_zero]
    ring
  have hsum :
      gap * (jxx + jyy) =
        measure * (2 * (((2 * Real.pi : ℝ) : ℂ)) *
          ((energyA * energyR - massA * massR) * factor)) *
          (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff) := by
    calc
      gap * (jxx + jyy) =
          gap * (measure * (∫ p in (0 : ℝ)..pMax, 2 * (p : ℂ) *
            (polarFourierZerothAngularKernel (p * 0 / hbar) *
              ((denominator p)⁻¹ * (energyA * energyR - massA * massR) * factor)))) := by
          rw [hdiag]
      _ = measure * (2 * (((2 * Real.pi : ℝ) : ℂ)) *
            ((energyA * energyR - massA * massR) * factor)) *
            (gap * (∫ p in (0 : ℝ)..pMax, (p : ℂ) * (denominator p)⁻¹)) := by
          rw [hrad]
          ring
      _ = _ := by rw [hlog]
  have hxx :
      gap * jxx = measure * (((2 * Real.pi : ℝ) : ℂ)) *
        ((energyA * energyR - massA * massR) * factor) *
        (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff) := by
    calc
      gap * jxx = (gap * (jxx + jyy)) / 2 := by rw [← hsymm]; ring
      _ = (measure * (2 * (((2 * Real.pi : ℝ) : ℂ)) *
        ((energyA * energyR - massA * massR) * factor)) *
        (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff)) / 2 := by rw [hsum]
      _ = _ := by ring
  constructor
  · exact hxx
  · exact (congrArg (fun j : ℂ => gap * j) hsymm).symm.trans hxx

/-- In the positive-real-spectral-center regime the finite-broadening RA
center gap is nonzero. Hence both physical origin crossed-current diagonal
coefficients have an explicit value, rather than only a gap-multiplied
identity. The physical Fourier measure appears once. The formula does not
evaluate nonzero-radius Fourier kernels or take disorder/regulator limits. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_eq_log
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
    let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let logDiff :=
      (Complex.log (finiteCutoffContinuumBornDysonDenominator
          .retarded v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
        Complex.log (finiteCutoffContinuumBornDysonDenominator
          .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) -
      (Complex.log (finiteCutoffContinuumBornDysonDenominator
          .advanced v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
        Complex.log (finiteCutoffContinuumBornDysonDenominator
          .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax))
    let value := gap⁻¹ * ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      (((2 * Real.pi : ℝ) : ℂ)) *
      ((energyA * energyR - massA * massR) * factor) *
      (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff))
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .x 0 v m probeEnergy broadening disorderStrength hbar pMax 0 = value) ∧
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax 0 = value) := by
  let energyR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let energyA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let massR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let massA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let gap := energyA ^ 2 - massA ^ 2 - (energyR ^ 2 - massR ^ 2)
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let logDiff :=
    (Complex.log (finiteCutoffContinuumBornDysonDenominator
        .retarded v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
      Complex.log (finiteCutoffContinuumBornDysonDenominator
        .retarded v m 0 0 probeEnergy broadening disorderStrength hbar pMax)) -
    (Complex.log (finiteCutoffContinuumBornDysonDenominator
        .advanced v m pMax 0 probeEnergy broadening disorderStrength hbar pMax) -
      Complex.log (finiteCutoffContinuumBornDysonDenominator
        .advanced v m 0 0 probeEnergy broadening disorderStrength hbar pMax))
  let value := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    (((2 * Real.pi : ℝ) : ℂ)) *
    ((energyA * energyR - massA * massR) * factor) *
    (-(((2 : ℂ) * (v : ℂ) ^ 2)⁻¹) * logDiff)
  let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
    .x 0 v m probeEnergy broadening disorderStrength hbar pMax 0
  let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
    .y 1 v m probeEnergy broadening disorderStrength hbar pMax 0
  have hgap : gap ≠ 0 :=
    finiteCutoffContinuumBornDysonRadial_center_gap_ne_zero_of_re_pos
      v m probeEnergy broadening disorderStrength hbar pMax
      hvelocity hbroadening hdisorder hpMax hcenterR
  have h := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_origin_diagonal_mul_center_gap_eq_log
    v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder hpMax hcenterR hcenterA
  dsimp only at h ⊢
  constructor
  · calc
      jxx = gap⁻¹ * (gap * jxx) := by field_simp [hgap]
      _ = gap⁻¹ * value := by rw [h.1]
  · calc
      jyy = gap⁻¹ * (gap * jyy) := by field_simp [hgap]
      _ = gap⁻¹ * value := by rw [h.2]

/-- Reconstruct the two diagonal Pauli coefficients of the finite-cutoff crossed current
from the independent isotropic `K0` and traceless `K2` radial integrals.
Both coefficients inherit the existing physical momentum measure exactly once.

This inverts the integrated sum/difference identity without taking a cutoff or
broadening limit; no `X` or `Psi` diagram has been evaluated. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let aA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let aR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let jxx := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let jyy := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    let isotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                2 * (p : ℂ) *
                  (polarFourierZerothAngularKernel (p * radius / hbar) *
                    ((aA p * aR p - dA p * dR p) * factor))
    let anisotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                2 * (p : ℂ) *
                  (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                    (bA p * bR p * factor))
    (jxx = (isotropic + anisotropic) / 2) ∧
      (jyy = (isotropic - anisotropic) / 2) := by
  have h :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_harmonics
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  dsimp only at h ⊢
  rcases h with ⟨h0, h2⟩
  constructor
  · linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h2
  · linear_combination (1 / 2 : ℂ) * h0 - (1 / 2 : ℂ) * h2


/-- The diagonal source-current product entering both crossed Hall minors
contains no mixed K0-K2 term. It is exactly a difference of squares of the
integrated isotropic K0 and traceless K2 radial moments. The momentum
measure is already included in both moments; no regulator is removed. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_product_eq_harmonic_squares
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let aA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let aR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let isotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
            ((aA p * aR p - dA p * dR p) * factor))
    let anisotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) * (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (bA p * bR p * factor))
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      (isotropic ^ 2 - anisotropic ^ 2) / 4 := by
  have h :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at h ⊢
  rcases h with ⟨hxx, hyy⟩
  rw [hxx, hyy]
  ring


/-- The antisymmetric source-scalar/diagonal-current minor needed in the
crossed X and Psi Hall amplitudes uses only the two K1 first-harmonic
scalar-current moments, the isotropic K0 moment, the traceless K2 moment,
and the independent transverse K0 current. The source-y diagonal channel
is (K0 - K2)/2; there are no additional Fourier measures or regulator limits. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_scalar_diagonal_minor_eq_harmonic_moments
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening disorderStrength hbar pMax
    let aA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let aR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let isotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
            ((aA p * aR p - dA p * dR p) * factor))
    let anisotropic :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          2 * (p : ℂ) * (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
            (bA p * bR p * factor))
    let firstX :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((aR p * bA p + aA p * bR p) * factor))
    let firstY :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((-Complex.I * (bR p * dA p - bA p * dR p)) * factor))
    let transverse :=
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        0 v m probeEnergy broadening disorderStrength hbar pMax radius *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        1 v m probeEnergy broadening disorderStrength hbar pMax radius *
      transverse =
      firstX * ((isotropic - anisotropic) / 2) - firstY * transverse := by
  have hfirst :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at hfirst hdiag ⊢
  rcases hfirst with ⟨hscalarX, hscalarY, _, _⟩
  rcases hdiag with ⟨_, hyy⟩
  rw [hscalarX, hscalarY, hyy]


end

end QuantumTheory.Models.MassiveDirac
