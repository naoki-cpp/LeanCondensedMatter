import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialHarmonics
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Radial Gaussian crossed trace kernels

This module reduces the model-specific finite-cutoff Gaussian crossed `X` / `Psi` trace kernels to
one-dimensional radial Green and current blocks on the real-space radial axis. The canonical
topology still contains `r ↦ -r`, but the massive-Dirac Green/current inversion laws eliminate
negative-radius Green/current blocks from the identities used by the antisymmetric Hall trace.

The radial Green/current Pauli coefficient bridges and their Fourier-harmonic identities live in
`Disorder.FiniteBroadeningBornRadialRealSpacePropagator` / `GaussianCrossedRadialCoefficients`
and `GaussianCrossedRadialHarmonics` respectively. This trace
module consumes them and reuses the canonical topology from `GaussianCrossedTrace`; it does not
redefine the `X` / `Psi` matrix products. The module retains the first-harmonic Fourier reduction and the Green/current minor identities
consumed by the antisymmetric Hall trace. No real-space angular integration, cutoff removal, broadening/disorder limit, or
conductivity normalization is introduced here.
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

/-- Local normalized radial Fourier recurrence consumed by the X and Psi trace reductions.
The public upstream identity retains its division-free normalization. -/
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
coefficient is a single K0-K2 momentum moment times the exact K1
Fourier recurrence factor. This does not alter the Fourier momentum
measure or take a regulator limit. -/
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
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at h
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax (-radius)] at h
  dsimp only
  rw [h]
  ring

/-- The second independent X Hall Green minor combines a Pauli-x and
a Pauli-scalar coefficient at negative real-space radius. The common
K1 factor reduces to a K0-K2 momentum moment without adding a new
Fourier measure or changing any finite regulator. -/
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

The factor `i (radius / hbar) / 2` is retained without dividing by radius
or assuming `hbar ≠ 0`. The finite cutoff, broadening, transverse current,
and physical momentum measure remain unchanged. -/
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
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax radius] at hzX hzY
  rw [hzX, hzY]
  ring

/-- The retarded/advanced Green transverse minor in the physical X Hall
amplitude has only K0 and K2 momentum moments. The first-harmonic
in-plane components share the explicit factor `i * (radius / hbar) / 2`,
which is factored out before the remaining real-space radius integral.

This identity keeps the physical Fourier momentum measure in *each* Green
block. It makes no assumption about the sign of `radius`, removes no
regulator, and does not evaluate the remaining radial integral. -/
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
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at hRz hAz
  simp only [neg_neg] at hRx hAx
  dsimp only at hRx hAx hRz hAz ⊢
  rw [hRx, hAx, hRz, hAz]
  ring

/-- On the real-space radial axis, the two-dimensional crossed trace kernel is exactly the radial
trace kernel assembled from the already reduced Green and current blocks. -/
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

/-- The radial `Psi` trace kernel remains real because its Hermitian-conjugate partner is included at
trace level. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
      .psi v m probeEnergy broadening disorderStrength hbar pMax radius).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
  exact gaussianCrossedTraceKernel_psi_im _ _ _ radius


end

end QuantumTheory.Models.MassiveDirac
