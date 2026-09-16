import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator

set_option linter.style.header false

/-!
# Finite-cutoff real-space Born-Dyson propagator

This module owns the real-space representation of the finite-cutoff finite-broadening Born-Dyson
Green matrix. The matrix Fourier transform is performed entrywise through the generic two-dimensional
physical-momentum polar Fourier transform, so the factor `d²p / (2πℏ)²` is already included in every
real-space Green block.

On the positive real-space radial axis, rotational symmetry reduces the angular Fourier integral to
the model-independent zeroth and first-cosine full-angle kernels from `Transport.Analysis.PolarFourier`.
The Green matrix supplies one `AngularHarmonicCoefficients` value at each radial momentum; entrywise
Fourier reduction consumes that common decomposition without rebuilding angular integrability.

No crossed-diagram topology, current vertex, real-space integration, cutoff removal, or conductivity
normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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

/-- One-dimensional radial-kernel representation of the finite-cutoff Born-Dyson Green matrix on
the positive real-space radial axis. The diagonal channels carry the zeroth angular kernel, while
the off-diagonal in-plane channel carries the first-cosine kernel. -/
noncomputable def finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : Matrix2 :=
  let a : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let prefactor : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let k0 : ℝ → ℂ := fun p =>
    polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 : ℝ → ℂ := fun p =>
    polarFourierFirstCosineAngularKernel (p * radius / hbar)
  !![
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k0 p * (a p + d p)),
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k1 p * b p);
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k1 p * b p),
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k0 p * (a p - d p))]

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
      entryHarmonics, harmonics, a, b, d] using
      (finiteCutoffPhysicalMomentumPolarFourier_radialAxis_harmonics
        hbar pMax radius (entryHarmonics 0 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 0 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 0 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d] using
      (finiteCutoffPhysicalMomentumPolarFourier_radialAxis_harmonics
        hbar pMax radius (entryHarmonics 0 1))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 0)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 0]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d] using
      (finiteCutoffPhysicalMomentumPolarFourier_radialAxis_harmonics
        hbar pMax radius (entryHarmonics 1 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d] using
      (finiteCutoffPhysicalMomentumPolarFourier_radialAxis_harmonics
        hbar pMax radius (entryHarmonics 1 1))

end

end QuantumTheory.Transport.Models.MassiveDirac
