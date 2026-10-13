import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialRealSpacePropagator

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

end

end QuantumTheory.Models.MassiveDirac
