import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
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

/-- The traceless second angular Fourier harmonic vanishes at the origin.
The result follows from the canonical full-angle harmonic integration theorem. -/
private theorem polarFourierSecondCosineAngularKernel_zero :
    polarFourierSecondCosineAngularKernel 0 = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 1
      secondMixed := 0 }
  have h := coefficients.integral_eval
  simpa [coefficients, AngularHarmonicCoefficients.eval,
    polarFourierSecondCosineAngularKernel, polarFourierRadialPhase,
    smul_eq_mul] using h

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


end

end QuantumTheory.Models.MassiveDirac
