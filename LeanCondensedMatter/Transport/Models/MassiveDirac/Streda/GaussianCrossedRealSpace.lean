import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornRealSpacePropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedTrace

set_option linter.style.header false

/-!
# Finite-cutoff real-space realization of Gaussian crossed Hall blocks

This module connects the crossed trace boundary to the massive-Dirac finite-cutoff finite-broadening
Born-Dyson data. The real-space Green field is consumed from the disorder-owned Born-Dyson
real-space propagator. The crossed current block applies the shared physical-momentum polar Fourier
transform entrywise to an advanced Green matrix, the diagonal crossed-sector in-plane Pauli vertex,
and a retarded Green matrix, in the order appearing in Ado et al., EPL 111, 37004 (2015), Eq. (14).

For the crossed sector, Eq. (14) uses only the diagonal factor `F = 1 / (1 - A)` of the dressed
current from Eq. (11). Accordingly the current block below resums only the longitudinal current-rung
coordinate and applies that common scalar to the requested Cartesian Pauli direction. The transverse
`F² B` part of the full local retarded-advanced dressed current, and the corresponding higher-order
feedback into the exact two-component fixed point, are deliberately not inserted into `J_r`.
On the positive real-space radial axis the quadratic angular product is represented by the shared
`AngularHarmonicCoefficients` adapter and reduced exactly to the zeroth, first-cosine, and
second-cosine full-angle radial Fourier kernels. The finite momentum cutoff and external broadening
remain explicit; no cutoff removal, zero-broadening limit, weak-disorder reduction, real-space `r`
integration, or crossed conductivity value is claimed here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Diagonal dressed-current factor used by the Gaussian crossed sector.

This is the finite-`η` diagonal ladder resummation `(1 - A)⁻¹`, where `A` is the longitudinal
source-`x` current-rung coefficient. It is the regularized repository counterpart of the factor `F`
retained in Ado et al. Eq. (14), rather than the complete two-component dressed-current fixed point. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (1 - finiteCutoffContinuumBornDysonCurrentRungVector
    v m probeEnergy broadening disorderStrength hbar pMax 0)⁻¹

@[simp]
theorem finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
      v m probeEnergy broadening 0 hbar pMax = 1 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor,
    finiteCutoffContinuumBornDysonCurrentRungVector]

private def gaussianCrossedCurrentCoefficientVector
    (source : Fin 2) (factor : ℂ) : InPlaneCoefficientVector :=
  fun direction => if direction = source then factor else 0

private theorem gaussianCrossedCurrentCoefficientVector_vertex
    (source : Fin 2) (factor : ℂ) :
    gaussianCrossedCurrentCoefficientVector source factor 0 • sigmaX +
        gaussianCrossedCurrentCoefficientVector source factor 1 • sigmaY =
      factor • directionPauli source := by
  fin_cases source <;>
    simp [gaussianCrossedCurrentCoefficientVector, directionPauli,
      inPlanePauliAxis, InternalSpace.pauliBasis]

/-- Scalar radial momentum kernel for one Gaussian-crossed current-block entry. The angular
harmonics have already been reduced to the finite-cutoff `K0` / `K1` / `K2` radial kernels. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) : ℂ :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let coefficients := gaussianCrossedCurrentCoefficientVector source factor
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics :=
    polarPauliInPlaneHarmonics aA bA dA aR bR dR coefficients
  (p : ℂ) *
    (polarFourierZerothAngularKernel (p * radius / hbar) * harmonics.constant i j +
      polarFourierFirstCosineAngularKernel (p * radius / hbar) * harmonics.firstCosine i j +
      polarFourierSecondCosineAngularKernel (p * radius / hbar) *
        harmonics.secondCosine i j)

/-- Source-indexed finite-cutoff finite-`η` Gaussian-crossed real-space current block.

This is the regularized massive-Dirac realization of the `J_r` object entering the crossed trace
kernel. Its Fourier integrand is `Gᴬ (F σ_source) Gᴿ`, with `F` supplied by the diagonal ladder
resummation above. The transverse component of the full local dressed vertex is intentionally absent,
matching the leading crossed-sector reduction used in Ado et al. Eq. (14). -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let vertex : Matrix2 := factor • directionPauli source
  fun i j =>
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
      (fun p θ =>
        (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          vertex *
          finiteCutoffContinuumBornDysonGreenMatrix
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) i j)
      r

/-- One-dimensional radial-kernel representation of the Gaussian crossed current block on the
positive real-space radial axis. Only the zeroth, first-cosine, and second-cosine channels survive. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : Matrix2 :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let coefficients := gaussianCrossedCurrentCoefficientVector source factor
  let aA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics : ℝ → AngularHarmonicCoefficients Matrix2 := fun p =>
    polarPauliInPlaneHarmonics
      (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients
  fun i j =>
    (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      ∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (polarFourierZerothAngularKernel (p * radius / hbar) * (harmonics p).constant i j +
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
              (harmonics p).firstCosine i j +
            polarFourierSecondCosineAngularKernel (p * radius / hbar) *
              (harmonics p).secondCosine i j)

/-- Scalar Pauli coefficient of a positive-radius Gaussian-crossed current block. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  InternalSpace.pauliScalarCoefficient
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      source v m probeEnergy broadening disorderStrength hbar pMax radius)

/-- Axis-indexed Pauli coefficient of a positive-radius Gaussian-crossed current block. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  InternalSpace.pauliVectorCoefficient
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      source v m probeEnergy broadening disorderStrength hbar pMax radius) axis

/-- Pointwise scalar Pauli kernel of the positive-axis Gaussian-crossed radial current integrand.
The source-x channel carries the first-cosine scalar harmonic, while source-y carries its mixed
partner. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) : ℂ :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let scalar := aR * bA + aA * bR
  let scalarMix := bR * dA - bA * dR
  let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
  if source = 0 then
    (p : ℂ) * (k1 * (scalar * factor))
  else
    (p : ℂ) * (k1 * (-Complex.I * scalarMix * factor))

/-- Pointwise Pauli-vector kernel of the positive-axis Gaussian-crossed radial current integrand.
The two source directions expose the explicit zeroth/first/second angular Fourier channels needed
by the crossed trace. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) : ℂ :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let aA := finiteCutoffContinuumBornDysonScalarCoefficient
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aR := finiteCutoffContinuumBornDysonScalarCoefficient
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR := finiteCutoffContinuumBornDysonPauliCoefficient .x
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR := finiteCutoffContinuumBornDysonPauliCoefficient .z
    .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let c0 := aA * aR - dA * dR
  let cxy := Complex.I * (aR * dA - aA * dR)
  let mass := bR * dA + bA * dR
  let massMix := aA * bR - aR * bA
  let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
  let k2 := polarFourierSecondCosineAngularKernel (p * radius / hbar)
  match axis with
  | .x =>
      if source = 0 then
        (p : ℂ) * (k0 * (c0 * factor) + k2 * (bA * bR * factor))
      else
        (p : ℂ) * (k0 * (-cxy * factor))
  | .y =>
      if source = 0 then
        (p : ℂ) * (k0 * (cxy * factor))
      else
        (p : ℂ) * (k0 * (c0 * factor) - k2 * (bA * bR * factor))
  | .z =>
      if source = 0 then
        (p : ℂ) * (k1 * (mass * factor))
      else
        (p : ℂ) * (k1 * (-Complex.I * massMix * factor))

/-- The pointwise Gaussian-crossed radial current entry kernel has the explicit scalar
first-cosine Pauli coefficient selected by the source direction. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliScalarCoefficient
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    InternalSpace.pauliScalarCoefficient
        (fun i j =>
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j) =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  fin_cases source <;>
    simp [InternalSpace.pauliScalarCoefficient,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel,
      gaussianCrossedCurrentCoefficientVector, polarPauliInPlaneHarmonics,
      sigmaX, sigmaY, sigmaZ, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ]
  all_goals ring

/-- The pointwise Gaussian-crossed radial current entry kernel has the explicit source-indexed
Pauli-vector coefficients in the zeroth, first-cosine, and second-cosine Fourier channels. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    InternalSpace.pauliVectorCoefficient
        (fun i j =>
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j) axis =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
        axis source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1 : ℂ) * Complex.I := by rw [hI2]
      _ = -Complex.I := by ring
  fin_cases source <;> cases axis <;>
    simp [InternalSpace.pauliVectorCoefficient,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel,
      gaussianCrossedCurrentCoefficientVector, polarPauliInPlaneHarmonics,
      sigmaX, sigmaY, sigmaZ, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ]
  all_goals
    ring_nf
    simp [hI2, hI3]

/-- Each entry of the Gaussian-crossed radial current block is the physical momentum-measure
prefactor times the integral of its scalar radial kernel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax radius i j =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j := by
  rfl

/-- The scalar Pauli coefficient of a radial crossed-current block is a scalar combination of its
entry-kernel integrals. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_entryKernel_integrals
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        source v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
          (∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
              source v m probeEnergy broadening disorderStrength hbar pMax radius p 0 0) +
        ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
          (∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
              source v m probeEnergy broadening disorderStrength hbar pMax radius p 1 1)) / 2 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
  rw [InternalSpace.pauliScalarCoefficient]
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral]

/-- Each Pauli-vector component of a radial crossed-current block is a scalar combination of its
entry-kernel integrals. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_entryKernel_integrals
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        axis source v m probeEnergy broadening disorderStrength hbar pMax radius =
      match axis with
      | .x =>
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  source v m probeEnergy broadening disorderStrength hbar pMax radius p 0 1) +
            ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  source v m probeEnergy broadening disorderStrength hbar pMax radius p 1 0)) / 2
      | .y =>
          Complex.I *
            (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
                (∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                    source v m probeEnergy broadening disorderStrength hbar pMax radius p 0 1) -
              ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
                (∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                    source v m probeEnergy broadening disorderStrength hbar pMax radius p 1 0)) / 2
      | .z =>
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  source v m probeEnergy broadening disorderStrength hbar pMax radius p 0 0) -
            ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  source v m probeEnergy broadening disorderStrength hbar pMax radius p 1 1)) / 2 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
  cases axis <;>
    simp only [InternalSpace.pauliVectorCoefficient] <;>
    rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral]

/-- The two-dimensional Fourier definition of the Gaussian crossed current block reduces exactly to
the one-dimensional zeroth/first/second radial kernels on the positive real-space radial axis. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius 0) =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax radius := by
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let coefficients := gaussianCrossedCurrentCoefficientVector source factor
  let aA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dA : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let aR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let bR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let dR : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics : ℝ → AngularHarmonicCoefficients Matrix2 := fun p =>
    polarPauliInPlaneHarmonics
      (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients
  let entryHarmonics : Fin 2 → Fin 2 → ℝ → AngularHarmonicCoefficients ℂ :=
    fun i j p =>
      { constant := (harmonics p).constant i j
        firstCosine := (harmonics p).firstCosine i j
        firstSine := (harmonics p).firstSine i j
        secondCosine := (harmonics p).secondCosine i j
        secondMixed := (harmonics p).secondMixed i j }
  have hA (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          .advanced v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix (aA p) (bA p) (dA p) θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, aA, bA, dA] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        .advanced v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have hR (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          .retarded v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix (aR p) (bR p) (dR p) θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, aR, bR, dR] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        .retarded v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have hvertex :
      coefficients 0 • sigmaX + coefficients 1 • sigmaY =
        factor • directionPauli source := by
    simpa [coefficients] using
      (gaussianCrossedCurrentCoefficientVector_vertex source factor)
  change
    (fun i j =>
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ =>
          (finiteCutoffContinuumBornDysonGreenMatrix
              .advanced v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax *
            (factor • directionPauli source) *
            finiteCutoffContinuumBornDysonGreenMatrix
              .retarded v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax) i j)
        (polarPoint2D radius 0)) =
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax radius
  apply Matrix.ext
  intro i j
  have hfield :
      (fun p θ =>
        (finiteCutoffContinuumBornDysonGreenMatrix
            .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax *
          (factor • directionPauli source) *
          finiteCutoffContinuumBornDysonGreenMatrix
            .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax) i j) =
        fun p θ => (entryHarmonics i j p).eval θ := by
    funext p θ
    rw [hA, hR, ← hvertex, polarPauliMatrix_inPlane_sandwich_eq_harmonics]
    simp [entryHarmonics, harmonics, AngularHarmonicCoefficients.eval,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfield]
  simpa [finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock,
    factor, coefficients, harmonics, entryHarmonics, aA, bA, dA, aR, bR, dR] using
    (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
      hbar pMax radius 0 (entryHarmonics i j))

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_neg_radius
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax (-radius) p i j =
      -(sigmaZ i i *
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p i j *
          sigmaZ j j) := by
  have harg : p * (-radius) / hbar = -(p * radius / hbar) := by
    ring
  fin_cases source <;> fin_cases i <;> fin_cases j <;>
    unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel <;>
    rw [harg] <;>
    simp [gaussianCrossedCurrentCoefficientVector, polarPauliInPlaneHarmonics,
      sigmaX, sigmaY, sigmaZ, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ]

/-- Reversing the radial coordinate changes the crossed current block by `σ_z`
conjugation together with the sign of the in-plane current insertion. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_neg_radius
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax (-radius) =
      -(sigmaZ *
          finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
            source v m probeEnergy broadening disorderStrength hbar pMax radius *
          sigmaZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, InternalSpace.pauliZ, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_neg_radius]

/-- Massive-Dirac finite-cutoff finite-`η` realization of the pointwise Gaussian crossed trace
kernel. The remaining real-space integral and conductivity normalization stay downstream. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : ℂ :=
  gaussianCrossedTraceKernel diagram
    (finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
      .retarded v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
      .advanced v m probeEnergy broadening disorderStrength hbar pMax)
    (fun source =>
      finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax)
    r

/-- The model-specific finite-cutoff `Psi` trace kernel remains real by the same trace-level
Hermitian-conjugate construction as the abstract crossed boundary. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
      .psi v m probeEnergy broadening disorderStrength hbar pMax r).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
  exact gaussianCrossedTraceKernel_psi_im _ _ _ r

end

end QuantumTheory.Transport.Models.MassiveDirac
