import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRadialHarmonics
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRadialTrace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpaceIntegral

set_option linter.style.header false

/-!
# Explicit harmonic moments of the Gaussian-crossed Hall traces

Pointwise antisymmetric X and Psi radial trace tensors reduce to their
finite-cutoff K0/K1/K2 Fourier-moment channels. The preceding
`GaussianCrossedRealSpaceIntegral` module owns the rotation, angular projection,
and regulated position-space integral boundaries; this module specializes
the resulting antisymmetric trace tensors to explicit harmonic moments.

The physical Fourier momentum measure remains inside its original current and
Green blocks. No final real-space integral, conductivity value, or regulator
limit is evaluated here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_diagonal_harmonic_squares
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let a := InternalSpace.pauliScalarCoefficient Jx
      let b := InternalSpace.pauliScalarCoefficient GR
      let c := InternalSpace.pauliScalarCoefficient Jy
      let d := InternalSpace.pauliScalarCoefficient GA
      let u := InternalSpace.pauliVectorCoefficient Jx
      let vr := InternalSpace.pauliVectorCoefficient GR
      let w := InternalSpace.pauliVectorCoefficient Jy
      let va := InternalSpace.pauliVectorCoefficient GA
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                 (bA p * bR p * factor))
      2 * Complex.I *
        ((a * w .y - c * u .y) * (vr .x * va .z - vr .z * va .x) +
          (b * va .z - d * vr .z) *
            ((isotropic ^ 2 - anisotropic ^ 2) / 4 + (u .y) ^ 2) +
          (d * vr .x - b * va .x) * (w .y * u .z - u .y * w .z)) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_transverse_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_product_eq_harmonic_squares
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hdiag
  rw [mul_comm
    (InternalSpace.pauliVectorCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        0 v m probeEnergy broadening disorderStrength hbar pMax radius) .x)
    (InternalSpace.pauliVectorCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y)] at hdiag
  dsimp only at hdiag ⊢
  rw [hdiag]
  ring

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_first_harmonic_minor
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let b := InternalSpace.pauliScalarCoefficient GR
      let d := InternalSpace.pauliScalarCoefficient GA
      let u := InternalSpace.pauliVectorCoefficient Jx
      let vr := InternalSpace.pauliVectorCoefficient GR
      let w := InternalSpace.pauliVectorCoefficient Jy
      let va := InternalSpace.pauliVectorCoefficient GA
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
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
      let moment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * radius / hbar) -
                 polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
      let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
      let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
      let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
      2 * Complex.I *
        ((firstX * ((isotropic - anisotropic) / 2) - firstY * u .y) *
            (vr .x * va .z - vr .z * va .x) +
          (b * va .z - d * vr .z) *
            ((isotropic ^ 2 - anisotropic ^ 2) / 4 + (u .y) ^ 2) +
          (d * vr .x - b * va .x) * (first * (w .y * zX - u .y * zY))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_diagonal_harmonic_squares
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hs :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_scalar_diagonal_minor_eq_harmonic_moments
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hz :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_z_minor_eq_k0_sub_k2
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hs hz
  dsimp only at hs hz ⊢
  rw [hs, hz]

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_green_harmonic_minors
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      let b := InternalSpace.pauliScalarCoefficient GR
      let d := InternalSpace.pauliScalarCoefficient GA
      let u := InternalSpace.pauliVectorCoefficient Jx
      let vr := InternalSpace.pauliVectorCoefficient GR
      let w := InternalSpace.pauliVectorCoefficient Jy
      let va := InternalSpace.pauliVectorCoefficient GA
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
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
      let moment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * radius / hbar) -
                 polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
      let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
      let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
      let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
      let greenBR := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .x
           .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenBA := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .x
           .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenDR := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .z
           .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenDA := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .z
           .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenFirst := Complex.I * ((((-radius) / hbar : ℝ) : ℂ)) / 2
      let greenSecondMoment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * (-radius) / hbar) -
                 polarFourierSecondCosineAngularKernel (p * (-radius) / hbar)) * f p)
      let greenZerothMoment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) * f p)
      let greenXZ := greenFirst *
         (greenSecondMoment greenBR * greenZerothMoment greenDA -
           greenZerothMoment greenDR * greenSecondMoment greenBA)
      let greenScalarX := greenFirst *
         (d * greenSecondMoment greenBR - b * greenSecondMoment greenBA)
      2 * Complex.I *
        ((firstX * ((isotropic - anisotropic) / 2) - firstY * u .y) *
            greenXZ +
          (b * va .z - d * vr .z) *
            ((isotropic ^ 2 - anisotropic ^ 2) / 4 + (u .y) ^ 2) +
          greenScalarX * (first * (w .y * zX - u .y * zY))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_first_harmonic_minor
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hxz :=
    finiteCutoffContinuumBornDysonRadialGreen_ra_xz_minor_eq_harmonic_moments
      v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hsx :=
    finiteCutoffContinuumBornDysonRadialGreen_ra_scalar_x_minor_eq_k0_sub_k2
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient] at hxz hsx
  dsimp only at hxz hsx ⊢
  rw [hxz, hsx]

/-- The finite-regulator X antisymmetric radial trace in explicit K0/K1/K2 moments.
No radial integration or regulator limit is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_explicit_k0_k1_k2_moments
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
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
      let moment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * radius / hbar) -
                 polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
      let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
      let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
      let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
      let greenBR := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .x
           .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenBA := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .x
           .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenDR := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .z
           .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenDA := fun p : ℝ =>
         finiteCutoffContinuumBornDysonPauliCoefficient .z
           .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
      let greenFirst := Complex.I * ((((-radius) / hbar : ℝ) : ℂ)) / 2
      let greenSecondMoment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * (-radius) / hbar) -
                 polarFourierSecondCosineAngularKernel (p * (-radius) / hbar)) * f p)
      let greenZerothMoment := fun f : ℝ → ℂ =>
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) * f p)
      let greenScalarR :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) *
               finiteCutoffContinuumBornDysonScalarCoefficient
                 .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let greenScalarA :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) *
               finiteCutoffContinuumBornDysonScalarCoefficient
                 .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let greenZR :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) *
               finiteCutoffContinuumBornDysonPauliCoefficient .z
                 .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let greenZA :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * (-radius) / hbar) *
               finiteCutoffContinuumBornDysonPauliCoefficient .z
                 .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let transverseX :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
               (Complex.I * (aR p * dA p - aA p * dR p) * factor))
      let diagonalY := (isotropic - anisotropic) / 2
      let greenXZ := greenFirst *
         (greenSecondMoment greenBR * greenZerothMoment greenDA -
           greenZerothMoment greenDR * greenSecondMoment greenBA)
      let greenScalarX := greenFirst *
         (greenScalarA * greenSecondMoment greenBR - greenScalarR * greenSecondMoment greenBA)
      2 * Complex.I *
        ((firstX * diagonalY - firstY * transverseX) *
            greenXZ +
          (greenScalarR * greenZA - greenScalarA * greenZR) *
            ((isotropic ^ 2 - anisotropic ^ 2) / 4 + transverseX ^ 2) +
          greenScalarX * (first * (diagonalY * zX - transverseX * zY))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_green_harmonic_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hsr :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hsa :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hzr :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hza :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  have hux :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hwy :=
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax).2
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hsr hsa hzr hza hux hwy
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarKernel] at hsr hsa
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at hzr hza
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel] at hux
  simp only [ite_true] at hux
  dsimp only at hsr hsa hzr hza hux hwy ⊢
  rw [hsr, hsa, hzr, hza, hux, hwy]


/-- The conjugate-symmetric part of the Psi Pauli triple is a real scalar.
The right-hand side is resolved into the real and imaginary Pauli minor
channels, ready for radial scalar-kernel analysis. -/
private theorem psi_conjugate_triple_half_eq_real_channels (z q : ℂ) :
    (8 * Complex.I * z * q +
        (starRingEnd ℂ) (8 * Complex.I * z * q)) / 2 =
      ((-8 * (z.re * q.im + z.im * q.re) : ℝ) : ℂ) := by
  apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.neg_re]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.neg_im]

/-- The regulated Psi antisymmetric radial trace expressed through real and imaginary minor channels. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_real_minor
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let a := InternalSpace.pauliScalarCoefficient Jx
      let b := InternalSpace.pauliScalarCoefficient GR
      let c := InternalSpace.pauliScalarCoefficient Jy
      let gx := InternalSpace.pauliVectorCoefficient GR .x
      let gz := InternalSpace.pauliVectorCoefficient GR .z
      let u := InternalSpace.pauliVectorCoefficient Jx
      let w := InternalSpace.pauliVectorCoefficient Jy
      let minor := gx * (a * w .y - c * u .y) -
        b * ((u .y) ^ 2 + u .x * w .y)
      ((-8 * (gz.re * minor.im + gz.im * minor.re) : ℝ) : ℂ) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_transverse_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  dsimp only
  rw [psi_conjugate_triple_half_eq_real_channels]

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_diagonal_harmonic_squares
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let a := InternalSpace.pauliScalarCoefficient Jx
      let b := InternalSpace.pauliScalarCoefficient GR
      let c := InternalSpace.pauliScalarCoefficient Jy
      let gx := InternalSpace.pauliVectorCoefficient GR .x
      let gz := InternalSpace.pauliVectorCoefficient GR .z
      let u := InternalSpace.pauliVectorCoefficient Jx
      let w := InternalSpace.pauliVectorCoefficient Jy
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                 (bA p * bR p * factor))
      let minor := gx * (a * w .y - c * u .y) -
         b * ((u .y) ^ 2 + (isotropic ^ 2 - anisotropic ^ 2) / 4)
      ((-8 * (gz.re * minor.im + gz.im * minor.re) : ℝ) : ℂ) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_real_minor
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_product_eq_harmonic_squares
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hdiag
  dsimp only at hdiag ⊢
  rw [hdiag]

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_first_harmonic_minors
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
      let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
         0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
         .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let b := InternalSpace.pauliScalarCoefficient GR
      let gz := InternalSpace.pauliVectorCoefficient GR .z
      let u := InternalSpace.pauliVectorCoefficient Jx
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
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
      let greenFirst := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
      let greenSecondMoment :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * radius / hbar) -
                 polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                 finiteCutoffContinuumBornDysonPauliCoefficient .x
                   .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let minor := (greenFirst * greenSecondMoment) *
         (firstX * ((isotropic - anisotropic) / 2) - firstY * u .y) -
         b * ((u .y) ^ 2 + (isotropic ^ 2 - anisotropic ^ 2) / 4)
      ((-8 * (gz.re * minor.im + gz.im * minor.re) : ℝ) : ℂ) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_diagonal_harmonic_squares
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hs :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_scalar_diagonal_minor_eq_harmonic_moments
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hgr :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_negRadius_eq_k0_sub_k2
      .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hbroadening hdisorder hpMax
  simp only [neg_neg] at hgr
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hs hgr
  dsimp only at hs hgr ⊢
  rw [hs, hgr]
/-- The finite-regulator Psi antisymmetric radial trace in explicit K0/K1/K2 moments.
No radial integration or regulator limit is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_explicit_k0_k1_k2_moments
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2 =
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
             2 * (p : ℂ) *
               (polarFourierZerothAngularKernel (p * radius / hbar) *
                 ((aA p * aR p - dA p * dR p) * factor))
      let anisotropic :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             2 * (p : ℂ) *
               (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
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
      let greenFirst := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
      let greenSecondMoment :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) ^ 2 *
               ((polarFourierZerothAngularKernel (p * radius / hbar) -
                 polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                 finiteCutoffContinuumBornDysonPauliCoefficient .x
                   .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let greenScalar :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
               finiteCutoffContinuumBornDysonScalarCoefficient
                 .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let greenZ :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
               finiteCutoffContinuumBornDysonPauliCoefficient .z
                 .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      let transverse :=
         (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
           ∫ p in (0 : ℝ)..pMax,
             (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
               (Complex.I * (aR p * dA p - aA p * dR p) * factor))
      let minor := (greenFirst * greenSecondMoment) *
         (firstX * ((isotropic - anisotropic) / 2) - firstY * transverse) -
         greenScalar * (transverse ^ 2 + (isotropic ^ 2 - anisotropic ^ 2) / 4)
      ((-8 * (greenZ.re * minor.im + greenZ.im * minor.re) : ℝ) : ℂ) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_first_harmonic_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  have hscalar :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have htransverse :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient] at hscalar hz htransverse
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarKernel] at hscalar
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at hz
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel] at htransverse
  simp only [ite_true] at htransverse
  dsimp only at hscalar hz htransverse ⊢
  rw [hscalar, hz, htransverse]


end

end QuantumTheory.Models.MassiveDirac
