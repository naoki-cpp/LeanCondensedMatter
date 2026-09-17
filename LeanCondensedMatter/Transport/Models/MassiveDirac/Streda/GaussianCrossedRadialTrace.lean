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
finite scalar sums over matrix entries, removing the remaining matrix multiplication and trace
operations before later radial-kernel evaluation. No real-space angular integration, cutoff removal,
broadening/disorder limit, or conductivity normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

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
