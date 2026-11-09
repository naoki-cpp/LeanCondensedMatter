import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialHarmonics
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Radial Gaussian crossed trace kernels

This module specializes the canonical Gaussian crossed `X` / `Psi` trace topology to
one-dimensional radial Green and current blocks. The massive-Dirac inversion laws handle
the negative-radius arguments in the X/Psi traces.

The first-harmonic Fourier recurrence gives K0-K2 moment identities for Green/current
Pauli minors in the antisymmetric Hall trace. The Cartesian-to-radial-axis identity
relates the two-dimensional trace to its radial form. Fourier coefficient properties
are supplied by the radial Green propagator and Gaussian-crossed harmonic layers.

No real-space angular integration, regulator limit, or conductivity normalization is
introduced here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport


/-- Pointwise crossed trace kernel written only in terms of the one-dimensional radial Green and
current blocks. Negative real-space arguments are represented by negative scalar radii. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  gaussianCrossedTraceKernel diagram
    (fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ)
    (fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ)
    (fun source ρ =>
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax ρ)
    radius

/-- The first-cosine Fourier moment equals a K0-K2 moment multiplied by
`i * (radius / hbar) / 2`. The identity requires no nonzero-radius hypothesis. -/
private theorem gaussianCrossedRadialFirstHarmonicIntegral_eq_difference
    (hbar pMax radius : ℝ) (f : ℝ → ℂ) :
    (∫ p in (0 : ℝ)..pMax,
      (p : ℂ) *
        (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
      ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)) := by
  have h := integral_polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
    hbar pMax radius f
  linear_combination (1 / 2 : ℂ) * h

/-- At negative real-space radius, the retarded or advanced Green Pauli-x
coefficient is a K0-K2 momentum moment times the first-harmonic Fourier factor.
The identity holds at finite cutoff and broadening with the physical momentum measure. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let first := Complex.I * ((((-radius) / hbar : ℝ) : ℂ)) / 2
    let moment :=
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * (-radius) / hbar) -
              polarFourierSecondCosineAngularKernel (p * (-radius) / hbar)) *
              finiteCutoffContinuumBornDysonPauliCoefficient .x
                side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        .x side v m probeEnergy broadening disorderStrength hbar pMax (-radius) =
      first * moment := by
  have h :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .x side v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel,
    finiteCutoffContinuumBornDysonRadialPauliData] at h
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax (-radius)] at h
  dsimp only
  rw [h]
  ring

/-- The scalar-x Green minor in the X Hall trace is a K0-K2 momentum
moment times the common first-harmonic Fourier factor at finite regulators. -/
theorem finiteCutoffContinuumBornDysonRadialGreen_ra_scalar_x_minor_eq_k0_sub_k2
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let moment := fun side : SpectralSide =>
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * (-radius) / hbar) -
              polarFourierSecondCosineAngularKernel (p * (-radius) / hbar)) *
              finiteCutoffContinuumBornDysonPauliCoefficient .x
                side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
    let first := Complex.I * ((((-radius) / hbar : ℝ) : ℂ)) / 2
    let rx := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
      .x .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    let ax := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
      .x .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    let r0 := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
      .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    let a0 := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
      .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    a0 * rx - r0 * ax =
      first * (a0 * moment .retarded - r0 * moment .advanced) := by
  have hR :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hA :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at hR hA ⊢
  rw [hR, hA]
  ring

/-- The Pauli-z/source-current minor appearing in the regulated crossed X Hall
trace has a common first-harmonic factor. The two source-z current coefficients
reduce from K1 to K0-K2 momentum integrals via the exact Fourier recurrence.

The identity uses the factor `i (radius / hbar) / 2` without imposing
`hbar ≠ 0` or a nonzero-radius hypothesis. Each current block carries its
physical momentum-measure prefactor. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_z_minor_eq_k0_sub_k2
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
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let moment := fun f : ℝ → ℂ =>
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * radius / hbar) -
              polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
    let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
    let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
    let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
    let uY := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let wY := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    wY * finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
      uY * finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      first * (wY * zX - uY * zY) := by
  have h :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at h ⊢
  rcases h with ⟨_, _, hzX, hzY⟩
  dsimp only [finiteCutoffContinuumBornDysonRadialPauliData] at hzX hzY
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax radius] at hzX hzY
  rw [hzX, hzY]
  ring

/-- The retarded/advanced Green transverse minor in the physical X Hall
amplitude has only K0 and K2 momentum moments. The first-harmonic
in-plane components share the explicit factor `i * (radius / hbar) / 2`,
which is factored out before the remaining real-space radius integral.

The identity is pointwise in the real-space radius at finite regulators,
with a physical Fourier momentum-measure prefactor in each Green block.
The real-space radial integral is not evaluated. -/
theorem finiteCutoffContinuumBornDysonRadialGreen_ra_xz_minor_eq_harmonic_moments
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
    let bR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let bA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dR := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
    let secondMoment := fun f : ℝ → ℂ =>
      prefactor * ∫ p in (0 : ℝ)..pMax,
        (p : ℂ) ^ 2 *
          ((polarFourierZerothAngularKernel (p * radius / hbar) -
            polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
    let zerothMoment := fun f : ℝ → ℂ =>
      prefactor * ∫ p in (0 : ℝ)..pMax,
        (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) * f p)
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius *
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        .z .advanced v m probeEnergy broadening disorderStrength hbar pMax radius -
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius *
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        .x .advanced v m probeEnergy broadening disorderStrength hbar pMax radius =
      first * (secondMoment bR * zerothMoment dA -
        zerothMoment dR * secondMoment bA) := by
  have hRx :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
      .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hAx :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
      .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hRz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hAz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel,
    finiteCutoffContinuumBornDysonRadialPauliData] at hRz hAz
  simp only [neg_neg] at hRx hAx
  dsimp only at hRx hAx hRz hAz ⊢
  rw [hRx, hAx, hRz, hAz]
  ring

/-- On the real-space radial axis, the two-dimensional crossed trace kernel equals
the trace of the radial Green and current blocks. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_radialAxis_eq
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
        diagram v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius 0) =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        diagram v m probeEnergy broadening disorderStrength hbar pMax radius := by
  have hneg := neg_polarPoint2D radius 0
  cases diagram <;>
    simp only [finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
      gaussianCrossedTraceKernel] <;>
    rw [hneg] <;>
    simp only [finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq,
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq]

/-- The radial `Psi` trace kernel is real because its definition includes the
Hermitian-conjugate partner. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
      .psi v m probeEnergy broadening disorderStrength hbar pMax radius).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
  exact gaussianCrossedTraceKernel_psi_im _ _ _ radius


end

end QuantumTheory.Models.MassiveDirac
