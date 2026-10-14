import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator
import LeanCondensedMatter.Models.MassiveDirac.Model.Rotation

set_option linter.style.header false

/-!
# Two-dimensional real-space Born-Dyson propagator

The finite-cutoff, finite-broadening Born-Dyson Green matrix is transformed entrywise by the
generic two-dimensional physical-momentum polar Fourier transform, with measure
`d²p / (2πℏ)²` already included in every real-space Green block.

The model-independent constant, first, and second angular-harmonic kernels support an
arbitrary polar real-space point. The radial-axis identity identifies this two-dimensional
representation with the one-dimensional Green matrix defined upstream in
`FiniteBroadeningBornRadialRealSpacePropagator`. The massive-Dirac Green matrix has vanishing
second-harmonic coefficients, and its first-sine channel vanishes on the radial axis.
The entrywise Fourier reduction reuses one `AngularHarmonicCoefficients` decomposition.

No crossed-diagram topology, current vertex, real-space integration, cutoff removal, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-cutoff finite-`η` real-space Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  fun i j =>
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
      (fun p θ =>
        finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j)
      r

/-- The finite-broadening Born-Dyson Green *momentum* matrix is spinor covariant.
This is pointwise in radial momentum and precedes any Fourier integration.
The radial-axis reference is the same regulated Green matrix at momentum `(p, 0)`. -/
theorem finiteCutoffContinuumBornDysonGreenMatrix_polar_spinRotation
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax p angle : ℝ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        side v m (p * Real.cos angle) (p * Real.sin angle)
        probeEnergy broadening disorderStrength hbar pMax =
      inPlaneSpinRotation angle *
        finiteCutoffContinuumBornDysonGreenMatrix
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax *
        inPlaneSpinRotationInverse angle := by
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have hpolar (θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix a b d θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, a, b, d] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        side v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have haxis :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix a b d 0 := by
    simpa using hpolar 0
  rw [hpolar angle, haxis]
  exact polarPauliMatrix_eq_spinRotation a b d angle

/-- Finite-cutoff angular Green entry kernel at an arbitrary polar real-space point.
The constant Pauli channels carry `K0`; the in-plane Pauli vector rotates as
`(cos angle, sin angle)` in the first Fourier harmonic `K1`. The physical
momentum measure is attached by the Fourier integral, not by this kernel. -/
noncomputable def finiteCutoffContinuumBornDysonAngularGreenEntryKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle p : ℝ)
    (i j : Fin 2) : ℂ :=
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  (p : ℂ) *
    (polarFourierZerothAngularKernel (p * radius / hbar) *
        (a • (1 : Matrix2) + d • sigmaZ) i j +
      polarFourierFirstCosineAngularKernel (p * radius / hbar) *
        (((Real.cos angle : ℝ) : ℂ) * (b • sigmaX) i j +
          (((Real.sin angle : ℝ) : ℂ)) * (b • sigmaY) i j))

/-- Algebraic spinor covariance of the K0/K1 polar momentum integrand.
Both the angular and radial-axis matrices are expressed with the same
canonical Pauli coefficients, avoiding any additional covariance hypothesis. -/
private theorem angularGreenPauliKernel_eq_spinRotation
    (momentum k0 k1 a b d : ℂ) (angle : ℝ) :
    (fun i j : Fin 2 =>
      momentum *
        (k0 * (a • (1 : Matrix2) + d • sigmaZ) i j +
          k1 * ((((Real.cos angle : ℝ) : ℂ)) * (b • sigmaX) i j +
            (((Real.sin angle : ℝ) : ℂ)) * (b • sigmaY) i j))) =
      inPlaneSpinRotation angle *
        (momentum • polarPauliMatrix (k0 * a) (k1 * b) (k0 * d) 0) *
        inPlaneSpinRotationInverse angle := by
  have hangular :
      (fun i j : Fin 2 =>
        momentum *
          (k0 * (a • (1 : Matrix2) + d • sigmaZ) i j +
            k1 * ((((Real.cos angle : ℝ) : ℂ)) * (b • sigmaX) i j +
              (((Real.sin angle : ℝ) : ℂ)) * (b • sigmaY) i j))) =
        momentum • polarPauliMatrix (k0 * a) (k1 * b) (k0 * d) angle := by
    ext i j
    simp only [polarPauliMatrix, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hangular, polarPauliMatrix_eq_spinRotation]
  simp only [mul_smul_comm, smul_mul_assoc]
  rfl

/-- The actual full-angle finite-cutoff Born-Dyson Green momentum kernel
is the spinor conjugate of its radial-axis Pauli K0/K1 kernel. The
physical momentum factor and radial Fourier coefficients remain unchanged.
The equality is **pointwise in radial momentum**, prior to any integration. -/
theorem finiteCutoffContinuumBornDysonAngularGreenEntryKernel_eq_spinRotation
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle p : ℝ) :
    let a := finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
    let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
    (fun i j : Fin 2 =>
      finiteCutoffContinuumBornDysonAngularGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax
        radius angle p i j) =
      inPlaneSpinRotation angle *
        ((p : ℂ) • polarPauliMatrix (k0 * a) (k1 * b) (k0 * d) 0) *
        inPlaneSpinRotationInverse angle := by
  dsimp only
  simpa only [finiteCutoffContinuumBornDysonAngularGreenEntryKernel] using
    (angularGreenPauliKernel_eq_spinRotation
      (p : ℂ)
      (polarFourierZerothAngularKernel (p * radius / hbar))
      (polarFourierFirstCosineAngularKernel (p * radius / hbar))
      (finiteCutoffContinuumBornDysonScalarCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .x
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonPauliCoefficient .z
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      angle)

/-- At an arbitrary real-space polar angle, the massive-Dirac Born-Dyson
Green matrix reduces entrywise to the canonical `K0`/`K1` channels.
This is the full-angle counterpart of the existing radial-axis identity
and does not assume an SO(2) rotation law. -/
theorem finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_eq_angularKernel_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius angle) i j =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonAngularGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius angle p i j := by
  let a : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics : ℝ → AngularHarmonicCoefficients Matrix2 := fun p =>
    { constant := a p • (1 : Matrix2) + d p • sigmaZ
      firstCosine := b p • sigmaX
      firstSine := b p • sigmaY
      secondCosine := 0
      secondMixed := 0 }
  let entryHarmonics : Fin 2 → Fin 2 → ℝ → AngularHarmonicCoefficients ℂ :=
    fun i j p =>
      { constant := (harmonics p).constant i j
        firstCosine := (harmonics p).firstCosine i j
        firstSine := (harmonics p).firstSine i j
        secondCosine := (harmonics p).secondCosine i j
        secondMixed := (harmonics p).secondMixed i j }
  have hpolar (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix (a p) (b p) (d p) θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, a, b, d] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        side v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have hfield (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        (harmonics p).eval θ := by
    rw [hpolar]
    simp [harmonics, AngularHarmonicCoefficients.eval, polarPauliMatrix]
    module
  have hentry (i j : Fin 2) (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j =
        (entryHarmonics i j p).eval θ := by
    have h := congrArg (fun M : Matrix2 => M i j) (hfield p θ)
    simpa [entryHarmonics, AngularHarmonicCoefficients.eval, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] using h
  change
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ =>
          finiteCutoffContinuumBornDysonGreenMatrix
            side v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening disorderStrength hbar pMax i j)
        (polarPoint2D radius angle) = _
  simp_rw [hentry i j]
  simpa [finiteCutoffContinuumBornDysonAngularGreenEntryKernel,
    entryHarmonics, harmonics, a, b, d, Matrix.zero_apply,
    smul_eq_mul] using
    (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
      hbar pMax radius angle (entryHarmonics i j))

/-- The two-dimensional polar Fourier representation of the finite-cutoff Born-Dyson Green matrix
reduces exactly to the one-dimensional zeroth/first angular kernels on the positive real-space
radial axis. -/
theorem finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius 0) =
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax radius := by
  let a : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics : ℝ → AngularHarmonicCoefficients Matrix2 := fun p =>
    { constant := a p • (1 : Matrix2) + d p • sigmaZ
      firstCosine := b p • sigmaX
      firstSine := b p • sigmaY
      secondCosine := 0
      secondMixed := 0 }
  let entryHarmonics : Fin 2 → Fin 2 → ℝ → AngularHarmonicCoefficients ℂ :=
    fun i j p =>
      { constant := (harmonics p).constant i j
        firstCosine := (harmonics p).firstCosine i j
        firstSine := (harmonics p).firstSine i j
        secondCosine := (harmonics p).secondCosine i j
        secondMixed := (harmonics p).secondMixed i j }
  have hpolar (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix (a p) (b p) (d p) θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, a, b, d] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        side v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have hfield (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        (harmonics p).eval θ := by
    rw [hpolar]
    simp [harmonics, AngularHarmonicCoefficients.eval, polarPauliMatrix]
    module
  have hentry (i j : Fin 2) (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j =
        (entryHarmonics i j p).eval θ := by
    have h := congrArg (fun M : Matrix2 => M i j) (hfield p θ)
    simpa [entryHarmonics, AngularHarmonicCoefficients.eval, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] using h
  funext i j
  fin_cases i <;> fin_cases j
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 0 0)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 0 0]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 0 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 0 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 0 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 0 1))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 0)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 0]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 1 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, sub_eq_add_neg, InternalSpace.pauliX,
      InternalSpace.pauliY, InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 1 1))


/-- Entrywise interval integration of a complex two-band matrix. The interval
integral's existing non-integrable convention is preserved entry by entry. -/
noncomputable def intervalIntegralMatrix2
    (a b : ℝ) (f : ℝ → Matrix2) : Matrix2 :=
  fun i j => ∫ p in a..b, f p i j

/-- Entrywise interval integration commutes with a fixed complex scalar. -/
theorem intervalIntegralMatrix2_smul
    (a b : ℝ) (c : ℂ) (f : ℝ → Matrix2) :
    intervalIntegralMatrix2 a b (fun p => c • f p) =
      c • intervalIntegralMatrix2 a b f := by
  ext i j
  change (∫ p in a..b, c * f p i j) = c * (∫ p in a..b, f p i j)
  rw [intervalIntegral.integral_const_mul]

/-- Entrywise interval integration is additive for interval-integrable matrices.
The assumptions matter: the default integral of a non-integrable function
is zero, so unconditional additivity would be false. -/
theorem intervalIntegralMatrix2_add
    (a b : ℝ) (f g : ℝ → Matrix2)
    (hf : ∀ i j, IntervalIntegrable (fun p => f p i j) MeasureTheory.volume a b)
    (hg : ∀ i j, IntervalIntegrable (fun p => g p i j) MeasureTheory.volume a b) :
    intervalIntegralMatrix2 a b (fun p => f p + g p) =
      intervalIntegralMatrix2 a b f + intervalIntegralMatrix2 a b g := by
  ext i j
  change (∫ p in a..b, f p i j + g p i j) =
    (∫ p in a..b, f p i j) + (∫ p in a..b, g p i j)
  exact intervalIntegral.integral_add (hf i j) (hg i j)

/-- Subtraction likewise commutes with entrywise interval integration
under the same explicit analytic assumptions. -/
theorem intervalIntegralMatrix2_sub
    (a b : ℝ) (f g : ℝ → Matrix2)
    (hf : ∀ i j, IntervalIntegrable (fun p => f p i j) MeasureTheory.volume a b)
    (hg : ∀ i j, IntervalIntegrable (fun p => g p i j) MeasureTheory.volume a b) :
    intervalIntegralMatrix2 a b (fun p => f p - g p) =
      intervalIntegralMatrix2 a b f - intervalIntegralMatrix2 a b g := by
  ext i j
  change (∫ p in a..b, f p i j - g p i j) =
    (∫ p in a..b, f p i j) - (∫ p in a..b, g p i j)
  exact intervalIntegral.integral_sub (hf i j) (hg i j)

/-- Diagonal spinor conjugation commutes with entrywise interval integration.
Every entry has only one nonzero summand, so scalar constant-factor integral
rules suffice and no additional integrability assumptions are required. -/
theorem intervalIntegralMatrix2_spinRotation_conjugate
    (angle a b : ℝ) (f : ℝ → Matrix2) :
    intervalIntegralMatrix2 a b
        (fun p => inPlaneSpinRotation angle * f p *
          inPlaneSpinRotationInverse angle) =
      inPlaneSpinRotation angle * intervalIntegralMatrix2 a b f *
        inPlaneSpinRotationInverse angle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [intervalIntegralMatrix2, inPlaneSpinRotation,
      inPlaneSpinRotationInverse, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_two, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, mul_assoc]

/-- At finite momentum cutoff, the fully integrated Born-Dyson Green matrix
inherits the spinor SO(2) covariance of its exact K0/K1 polar Fourier kernel.
The reference is the same two-dimensional Fourier Green matrix at angle zero.
Neither a new physical assumption nor a regulator limit is introduced. -/
theorem finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_spinRotation
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle : ℝ) :
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius angle) =
      inPlaneSpinRotation angle *
        finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius 0) *
        inPlaneSpinRotationInverse angle := by
  let base : ℝ → Matrix2 := fun p =>
    let a := finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
    let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
    (p : ℂ) • polarPauliMatrix (k0 * a) (k1 * b) (k0 * d) 0
  let angular : ℝ → ℝ → Matrix2 := fun θ p =>
    fun i j =>
      finiteCutoffContinuumBornDysonAngularGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax
        radius θ p i j
  have hpoint (θ p : ℝ) :
      angular θ p =
        inPlaneSpinRotation θ * base p * inPlaneSpinRotationInverse θ := by
    change
      (fun i j : Fin 2 =>
        finiteCutoffContinuumBornDysonAngularGreenEntryKernel
          side v m probeEnergy broadening disorderStrength hbar pMax
          radius θ p i j) =
        inPlaneSpinRotation θ *
          ((p : ℂ) • polarPauliMatrix
            (polarFourierZerothAngularKernel (p * radius / hbar) *
              finiteCutoffContinuumBornDysonScalarCoefficient
                side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
              finiteCutoffContinuumBornDysonPauliCoefficient .x
                side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
            (polarFourierZerothAngularKernel (p * radius / hbar) *
              finiteCutoffContinuumBornDysonPauliCoefficient .z
                side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
            0) *
          inPlaneSpinRotationInverse θ
    exact
      finiteCutoffContinuumBornDysonAngularGreenEntryKernel_eq_spinRotation
        side v m probeEnergy broadening disorderStrength hbar pMax radius θ p
  have hU0 : inPlaneSpinRotation 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [inPlaneSpinRotation]
  have hU0inv : inPlaneSpinRotationInverse 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [inPlaneSpinRotationInverse]
  have hpoint0 (p : ℝ) : angular 0 p = base p := by
    simpa only [hU0, hU0inv, one_mul, mul_one] using hpoint 0 p
  let prefactor : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hIntegral (θ : ℝ) :
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius θ) =
        prefactor • intervalIntegralMatrix2 0 pMax (angular θ) := by
    ext i j
    change
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius θ) i j =
        prefactor * ∫ p in (0 : ℝ)..pMax, angular θ p i j
    exact finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_eq_angularKernel_integral
      side v m probeEnergy broadening disorderStrength hbar pMax radius θ i j
  have hrot :
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius angle) =
        prefactor •
          (inPlaneSpinRotation angle * intervalIntegralMatrix2 0 pMax base *
            inPlaneSpinRotationInverse angle) := by
    rw [hIntegral angle]
    have hentries :
        intervalIntegralMatrix2 0 pMax (angular angle) =
          intervalIntegralMatrix2 0 pMax
            (fun p => inPlaneSpinRotation angle * base p *
              inPlaneSpinRotationInverse angle) := by
      ext i j
      apply intervalIntegral.integral_congr
      intro p _
      exact congrArg (fun M : Matrix2 => M i j) (hpoint angle p)
    rw [hentries, intervalIntegralMatrix2_spinRotation_conjugate]
  have haxis :
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius 0) =
        prefactor • intervalIntegralMatrix2 0 pMax base := by
    rw [hIntegral 0]
    congr 1
    ext i j
    apply intervalIntegral.integral_congr
    intro p _
    exact congrArg (fun M : Matrix2 => M i j) (hpoint0 p)
  rw [hrot, haxis]
  simp only [mul_smul_comm, smul_mul_assoc]

/-- Full model-specific SO(2) covariance relative to the canonical
one-dimensional radial Green matrix, valid for retarded and advanced sides. -/
theorem finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_eq_radial_spinRotation
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle : ℝ) :
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius angle) =
      inPlaneSpinRotation angle *
        finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax radius *
        inPlaneSpinRotationInverse angle := by
  rw [finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_spinRotation,
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq]

end

end QuantumTheory.Models.MassiveDirac
