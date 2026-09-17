import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial Gaussian crossed trace kernels

This module reduces the model-specific finite-cutoff Gaussian crossed `X` / `Psi` trace kernels to
one-dimensional radial Green and current blocks on the real-space radial axis. The sign change in
`-r` is kept explicitly as the scalar radius `-radius`; no parity property of the radial Fourier
kernels is assumed here.

The radial specialization reuses the canonical topology from `GaussianCrossedTrace`; it does not
redefine the `X` / `Psi` matrix products. The two radial topologies are additionally exposed as
finite scalar sums over matrix entries and then as products of one-dimensional scalar momentum
integrals. No real-space angular integration, cutoff removal, broadening/disorder limit, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Scalar radial momentum kernel for one Green-matrix entry in the crossed calculation. The
physical momentum-measure prefactor remains outside the one-dimensional integral. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) : ℂ :=
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
  (p : ℂ) *
    (!![k0 * (a + d), k1 * b;
        k1 * b, k0 * (a - d)] : Matrix2) i j

/-- Scalar radial momentum kernel for one Gaussian-crossed current-block entry. The angular
harmonics have already been reduced to the finite-cutoff `K0` / `K1` / `K2` radial kernels. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) : ℂ :=
  let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
    v m probeEnergy broadening disorderStrength hbar pMax
  let coefficients : InPlaneCoefficientVector :=
    fun direction => if direction = source then factor else 0
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

private theorem finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax radius i j =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral
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

private theorem trace_four_mul_eq_entry_sum (A B C D : Matrix2) :
    Matrix.trace (A * B * C * D) =
      ∑ i : Fin 2, ∑ l : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
        A i j * B j k * C k l * D l i := by
  simp [Matrix.trace, Matrix.mul_apply, mul_assoc]
  ring

/-- The radial `X` topology is a finite scalar sum of radial Green/current matrix entries. This
removes the remaining matrix multiplication and trace operations without changing any regulator or
Fourier normalization. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_entry_sum
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      ∑ i : Fin 2, ∑ l : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
        finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
            0 v m probeEnergy broadening disorderStrength hbar pMax radius i j *
          finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
            .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius) j k *
          finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
            1 v m probeEnergy broadening disorderStrength hbar pMax radius k l *
          finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
            .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius) l i := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  exact trace_four_mul_eq_entry_sum _ _ _ _

/-- The radial `X` topology is a finite sum of products of one-dimensional scalar momentum
integrals. Each real-space Fourier block retains exactly one physical momentum-measure prefactor. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_scalar_radial_kernels
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      ∑ i : Fin 2, ∑ l : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
        ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                0 v m probeEnergy broadening disorderStrength hbar pMax radius p i j) *
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
                .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius) p j k) *
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                1 v m probeEnergy broadening disorderStrength hbar pMax radius p k l) *
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
                .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius) p l i) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_entry_sum]
  simp_rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

/-- The radial `Psi` topology is the Hermitian-conjugate pair of one finite scalar entry sum. The
entry sum is the scalar boundary consumed by later radial-kernel evaluation. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_entry_sum
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let amplitude :=
        ∑ i : Fin 2, ∑ l : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
              0 v m probeEnergy broadening disorderStrength hbar pMax radius i j *
            finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
              .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius) j k *
            finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
              .retarded v m probeEnergy broadening disorderStrength hbar pMax radius k l *
            finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
              1 v m probeEnergy broadening disorderStrength hbar pMax (-radius) l i
      amplitude + (starRingEnd ℂ) amplitude := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  rw [trace_four_mul_eq_entry_sum]

/-- The radial `Psi` amplitude is a finite sum of products of one-dimensional scalar momentum
integrals; the full kernel adds its complex-conjugate partner. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_scalar_radial_kernels
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let amplitude :=
        ∑ i : Fin 2, ∑ l : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  0 v m probeEnergy broadening disorderStrength hbar pMax radius p i j) *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
                  .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius) p j k) *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialGreenEntryKernel
                  .retarded v m probeEnergy broadening disorderStrength hbar pMax radius p k l) *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  1 v m probeEnergy broadening disorderStrength hbar pMax (-radius) p l i)
      amplitude + (starRingEnd ℂ) amplitude := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_entry_sum]
  simp_rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

private theorem neg_polarPoint2D_zero (radius : ℝ) :
    -(polarPoint2D radius 0) = polarPoint2D (-radius) 0 := by
  funext i
  fin_cases i <;> simp [polarPoint2D]

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
  have hneg := neg_polarPoint2D_zero radius
  cases diagram with
  | x =>
      simp only [finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel,
        finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
        gaussianCrossedTraceKernel]
      rw [hneg,
        finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq,
        finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq,
        finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq,
        finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq]
  | psi =>
      simp only [finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel,
        finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
        gaussianCrossedTraceKernel]
      rw [hneg,
        finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq,
        finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq,
        finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq,
        finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_radialAxis_eq]

/-- The radial `Psi` trace kernel remains real because its Hermitian-conjugate partner is included at
trace level. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
      .psi v m probeEnergy broadening disorderStrength hbar pMax radius).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
  exact gaussianCrossedTraceKernel_psi_im _ _ _ radius

end

end QuantumTheory.Transport.Models.MassiveDirac
