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
On the positive real-space radial axis the quadratic angular product is reduced exactly to the
zeroth, first-cosine, and second-cosine full-angle radial Fourier kernels. The finite momentum cutoff
and external broadening remain explicit; no cutoff removal, zero-broadening limit, weak-disorder
reduction, real-space `r` integration, or crossed conductivity value is claimed here.
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
    simp [gaussianCrossedCurrentCoefficientVector, directionPauli]

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
  let c0 : ℝ → Matrix2 := fun p =>
    polarPauliInPlaneConstantAngularCoefficient
      (aA p) (dA p) (aR p) (dR p) coefficients
  let c1 : ℝ → Matrix2 := fun p =>
    polarPauliInPlaneFirstCosineAngularCoefficient
      (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients
  let c2 : ℝ → Matrix2 := fun p =>
    polarPauliInPlaneSecondCosineAngularCoefficient (bA p) (bR p) coefficients
  fun i j =>
    (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      ∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (polarFourierZerothAngularKernel (p * radius / hbar) * c0 p i j +
            polarFourierFirstCosineAngularKernel (p * radius / hbar) * c1 p i j +
            polarFourierSecondCosineAngularKernel (p * radius / hbar) * c2 p i j)

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
        fun p θ =>
          polarPauliInPlaneConstantAngularCoefficient
              (aA p) (dA p) (aR p) (dR p) coefficients i j +
            ((Real.cos θ : ℝ) : ℂ) *
              polarPauliInPlaneFirstCosineAngularCoefficient
                (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients i j +
            ((Real.sin θ : ℝ) : ℂ) *
              polarPauliInPlaneFirstSineAngularCoefficient
                (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients i j +
            ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) *
              polarPauliInPlaneSecondCosineAngularCoefficient
                (bA p) (bR p) coefficients i j +
            (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
              polarPauliInPlaneSecondMixedAngularCoefficient
                (bA p) (bR p) coefficients i j := by
    funext p θ
    rw [hA, hR, ← hvertex, polarPauliMatrix_inPlane_sandwich_eq_harmonics]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfield]
  simpa [finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock,
    factor, coefficients, aA, bA, dA, aR, bR, dR] using
    (finiteCutoffPhysicalMomentumPolarFourier_radialAxis_second_harmonics
      hbar pMax radius
      (fun p => polarPauliInPlaneConstantAngularCoefficient
        (aA p) (dA p) (aR p) (dR p) coefficients i j)
      (fun p => polarPauliInPlaneFirstCosineAngularCoefficient
        (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients i j)
      (fun p => polarPauliInPlaneFirstSineAngularCoefficient
        (aA p) (bA p) (dA p) (aR p) (bR p) (dR p) coefficients i j)
      (fun p => polarPauliInPlaneSecondCosineAngularCoefficient
        (bA p) (bR p) coefficients i j)
      (fun p => polarPauliInPlaneSecondMixedAngularCoefficient
        (bA p) (bR p) coefficients i j))

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
