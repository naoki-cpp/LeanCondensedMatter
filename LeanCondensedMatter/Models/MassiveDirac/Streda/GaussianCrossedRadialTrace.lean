import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRadialHarmonics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial Gaussian crossed trace kernels

This module reduces the model-specific finite-cutoff Gaussian crossed `X` / `Psi` trace kernels to
one-dimensional radial Green and current blocks on the real-space radial axis. The canonical
topology still contains `r ↦ -r`, but the massive-Dirac Green/current inversion laws eliminate
negative-radius blocks from the scalar entry-sum and radial-kernel evaluation boundaries.

The radial Green/current Pauli coefficient bridges and their Fourier-harmonic identities live in
`GaussianCrossedRadialCoefficients` and `GaussianCrossedRadialHarmonics` respectively. This trace
module consumes them and reuses the canonical topology from `GaussianCrossedTrace`; it does not
redefine the `X` / `Psi` matrix products. The two radial topologies are additionally exposed as
finite scalar sums over matrix entries and then as products of one-dimensional scalar momentum
integrals. No real-space angular integration, cutoff removal, broadening/disorder limit, or
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

private theorem trace_four_mul_eq_entry_sum
    {ι : Type*} [Fintype ι] (A B C D : Matrix ι ι ℂ) :
    Matrix.trace (A * B * C * D) =
      ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
        A i j * B j k * C k l * D l i := by
  simp [Matrix.trace, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem sigmaZ_conjugate_apply (M : Matrix2) (i j : Fin 2) :
    (sigmaZ * M * sigmaZ) i j = sigmaZ i i * M i j * sigmaZ j j := by
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, InternalSpace.pauliZ, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_two]


/-- The radial `X` topology is a finite scalar sum of positive-radius Green/current entries.
The two negative-radius Green blocks are replaced by their exact `σ_z` conjugates. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_entry_sum
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
        finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
            0 v m probeEnergy broadening disorderStrength hbar pMax radius i j *
          (sigmaZ j j *
            finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
              .retarded v m probeEnergy broadening disorderStrength hbar pMax radius j k *
            sigmaZ k k) *
          finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
            1 v m probeEnergy broadening disorderStrength hbar pMax radius k l *
          (sigmaZ l l *
            finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
              .advanced v m probeEnergy broadening disorderStrength hbar pMax radius l i *
            sigmaZ i i) := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  simp_rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius]
  rw [trace_four_mul_eq_entry_sum]
  simp_rw [sigmaZ_conjugate_apply]

/-- The radial `X` topology is a finite sum of products of positive-radius one-dimensional
scalar momentum integrals. Each real-space Fourier block retains exactly one physical
momentum-measure prefactor. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_scalar_radial_kernels
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
        ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                0 v m probeEnergy broadening disorderStrength hbar pMax radius p i j) *
          (sigmaZ j j *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  .retarded v m probeEnergy broadening disorderStrength hbar pMax radius p j k) *
            sigmaZ k k) *
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
            ∫ p in (0 : ℝ)..pMax,
              finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                1 v m probeEnergy broadening disorderStrength hbar pMax radius p k l) *
          (sigmaZ l l *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  .advanced v m probeEnergy broadening disorderStrength hbar pMax radius p l i) *
            sigmaZ i i) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_entry_sum]
  simp_rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

/-- The radial `Psi` topology is the Hermitian-conjugate pair of one positive-radius finite
scalar entry sum. The negative-radius Green and current blocks are replaced by their exact
`σ_z` conjugation laws. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_entry_sum
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let amplitude :=
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
              0 v m probeEnergy broadening disorderStrength hbar pMax radius i j *
            (sigmaZ j j *
              finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax radius j k *
              sigmaZ k k) *
            finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
              .retarded v m probeEnergy broadening disorderStrength hbar pMax radius k l *
            (-(sigmaZ l l *
              finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius l i *
              sigmaZ i i))
      amplitude + (starRingEnd ℂ) amplitude := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  simp_rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_neg_radius]
  rw [trace_four_mul_eq_entry_sum]
  simp_rw [Matrix.neg_apply, sigmaZ_conjugate_apply]

/-- The radial `Psi` amplitude is a finite sum of products of positive-radius one-dimensional
scalar momentum integrals; the full kernel adds its complex-conjugate partner. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_scalar_radial_kernels
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let amplitude :=
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
          ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                  0 v m probeEnergy broadening disorderStrength hbar pMax radius p i j) *
            (sigmaZ j j *
              ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                ∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius p j k) *
              sigmaZ k k) *
            ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
              ∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  .retarded v m probeEnergy broadening disorderStrength hbar pMax radius p k l) *
            (-(sigmaZ l l *
              ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                ∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
                    1 v m probeEnergy broadening disorderStrength hbar pMax radius p l i) *
              sigmaZ i i))
      amplitude + (starRingEnd ℂ) amplitude := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_entry_sum]
  simp_rw [
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

/-- The radial `X` trace is a closed scalar expression in the canonical Pauli coefficients
of the four positive-radius blocks. The two Green vectors are transformed by the exact `σ_z`
conjugation action, so no negative-radius block or matrix trace remains on the right-hand side. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_pauli_scalar
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      let a :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let b :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let c :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let d :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      let u := fun axis =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          axis 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let vr :=
        InternalSpace.pauliZConjugateVector (fun axis =>
          finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
            axis .retarded v m probeEnergy broadening disorderStrength hbar pMax radius)
      let w := fun axis =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          axis 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let va :=
        InternalSpace.pauliZConjugateVector (fun axis =>
          finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
            axis .advanced v m probeEnergy broadening disorderStrength hbar pMax radius)
      2 *
        ((a * b + dotProduct u vr) * (c * d + dotProduct w va) +
          dotProduct
            (a • vr + b • u + Complex.I • InternalSpace.pauliCross u vr)
            (c • va + d • w + Complex.I • InternalSpace.pauliCross w va)) := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  simp_rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius]
  rw [InternalSpace.trace_four_eq_pauliCoefficients]
  simp only [InternalSpace.pauliScalarCoefficient_pauliZ_conjugate,
    InternalSpace.pauliVectorCoefficient_pauliZ_conjugate,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient]

/-- The radial `X` amplitude is the explicit scalar expansion of the generic Pauli reduction.
The expansion uses the vanishing y component of the positive-radius Green blocks and the
crossed-current transverse antisymmetry to eliminate one independent Pauli component. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_explicit_pauli_components
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
      let a :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let b :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let c :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let d :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      let ux :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let uy :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let uz :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let wx := -uy
      let wy :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let wz :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let grx :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let grz :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let gax :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .x .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      let gaz :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .z .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
      2 *
        ((a * b - ux * grx + uz * grz) * (c * d - wx * gax + wz * gaz) +
          (-a * grx + b * ux + Complex.I * uy * grz) *
            (-c * gax + d * wx + Complex.I * wy * gaz) +
          (b * uy - Complex.I * (uz * grx + ux * grz)) *
            (d * wy - Complex.I * (wz * gax + wx * gaz)) +
          (a * grz + b * uz + Complex.I * uy * grx) *
            (c * gaz + d * wz + Complex.I * wy * gax)) := by
  have hoffdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_y_zero_eq_neg_x_one
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hret_y :
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .y .retarded v m probeEnergy broadening disorderStrength hbar pMax radius = 0 := by
    unfold finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
    simp [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      InternalSpace.pauliVectorCoefficient]
  have hadv_y :
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .y .advanced v m probeEnergy broadening disorderStrength hbar pMax radius = 0 := by
    unfold finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
    simp [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      InternalSpace.pauliVectorCoefficient]
  have hret_fun :
      (fun axis =>
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          axis .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) =
        (fun axis =>
          match axis with
          | .x => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
          | .y => 0
          | .z => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) := by
    funext axis
    cases axis
    · rfl
    · exact hret_y
    · rfl
  have hadv_fun :
      (fun axis =>
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          axis .advanced v m probeEnergy broadening disorderStrength hbar pMax radius) =
        (fun axis =>
          match axis with
          | .x => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .x .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
          | .y => 0
          | .z => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .z .advanced v m probeEnergy broadening disorderStrength hbar pMax radius) := by
    funext axis
    cases axis
    · rfl
    · exact hadv_y
    · rfl
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_pauli_scalar]
  rw [hret_fun, hadv_fun]
  simp [InternalSpace.pauliZConjugateVector, InternalSpace.dotProduct_pauliAxis,
    InternalSpace.pauliCross, cross_apply, InternalSpace.pauliAxisComponent, hoffdiag]; ring

/-- The radial `Psi` amplitude is a closed scalar Pauli-coefficient expression plus its complex
conjugate. The final current vector and scalar carry the overall sign from
`J_y(-r) = -σ_z J_y(r) σ_z`; all blocks on the right are evaluated at positive radius. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_pauli_scalar
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let a :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let b :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let c := b
      let d :=
        -finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let u := fun axis =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          axis 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let vr :=
        InternalSpace.pauliZConjugateVector (fun axis =>
          finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
            axis .retarded v m probeEnergy broadening disorderStrength hbar pMax radius)
      let w := fun axis =>
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          axis .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let vy :=
        -InternalSpace.pauliZConjugateVector (fun axis =>
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
            axis 1 v m probeEnergy broadening disorderStrength hbar pMax radius)
      let amplitude :=
        2 *
          ((a * b + dotProduct u vr) * (c * d + dotProduct w vy) +
            dotProduct
              (a • vr + b • u + Complex.I • InternalSpace.pauliCross u vr)
              (c • vy + d • w + Complex.I • InternalSpace.pauliCross w vy))
      amplitude + (starRingEnd ℂ) amplitude := by
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel,
    gaussianCrossedTraceKernel]
  simp_rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock_neg_radius]
  rw [InternalSpace.trace_four_eq_pauliCoefficients]
  simp only [InternalSpace.pauliScalarCoefficient_pauliZ_conjugate,
    InternalSpace.pauliVectorCoefficient_pauliZ_conjugate,
    InternalSpace.pauliScalarCoefficient_neg, InternalSpace.pauliVectorCoefficient_neg,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient,
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient]

/-- The radial `Psi` amplitude is the explicit scalar expansion of the generic Pauli reduction.
The positive-radius retarded Green y component is zero; transverse crossed-current
antisymmetry removes one independent component, and the radial current sign is kept explicit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_explicit_pauli_components
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
      let a :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let b :=
        finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let c := b
      let d :=
        -finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
          1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let ux :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .x 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let uy :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let uz :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius
      let qx := -uy
      let qy :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let qz :=
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
          .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius
      let grx :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let grz :=
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
      let amplitude :=
        2 *
          ((a * b - ux * grx + uz * grz) * (c * d + grx * qx - grz * qz) +
            (-a * grx + b * ux + Complex.I * uy * grz) *
              (c * qx + d * grx - Complex.I * grz * qy) +
            (b * uy - Complex.I * (uz * grx + ux * grz)) *
              (c * qy + Complex.I * (grz * qx + grx * qz)) +
            (a * grz + b * uz + Complex.I * uy * grx) *
              (-c * qz + d * grz + Complex.I * grx * qy))
      amplitude + (starRingEnd ℂ) amplitude := by
  have hoffdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_y_zero_eq_neg_x_one
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hret_y :
      finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          .y .retarded v m probeEnergy broadening disorderStrength hbar pMax radius = 0 := by
    unfold finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
    simp [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      InternalSpace.pauliVectorCoefficient]
  have hret_fun :
      (fun axis =>
        finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
          axis .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) =
        (fun axis =>
          match axis with
          | .x => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
          | .y => 0
          | .z => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
              .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius) := by
    funext axis
    cases axis
    · rfl
    · exact hret_y
    · rfl
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_pauli_scalar]
  rw [hret_fun]
  simp [InternalSpace.pauliZConjugateVector, InternalSpace.dotProduct_pauliAxis,
    InternalSpace.pauliCross, cross_apply, InternalSpace.pauliAxisComponent, hoffdiag]; ring

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
  calc
    (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
        (2 * (∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p))) / 2 := by
      ring
    _ = (Complex.I * (((radius / hbar : ℝ) : ℂ)) *
        (∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p))) / 2 := by
      rw [h]
    _ = _ := by ring

/-- The two antisymmetric source-current minors entering the physical crossed
Hall traces share an exact first-harmonic factor. The four scalar/z current
coefficients are reduced from K1 to K0-K2 radial momentum moments, leaving
the transverse source-current coefficients unchanged.

The factor `i (radius / hbar) / 2` is retained without dividing by
`radius` or assuming `hbar ≠ 0`. The identity holds at finite broadening
and finite momentum cutoff, before any real-space integration or limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_minors_eq_k0_sub_k2
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
    let scalarX := moment (fun p => (aR p * bA p + aA p * bR p) * factor)
    let scalarY := moment (fun p => (-Complex.I * (bR p * dA p - bA p * dR p)) * factor)
    let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
    let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
    let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
    let uY := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let wY := finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
      .y 1 v m probeEnergy broadening disorderStrength hbar pMax radius
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        0 v m probeEnergy broadening disorderStrength hbar pMax radius * wY -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        1 v m probeEnergy broadening disorderStrength hbar pMax radius * uY =
      first * (scalarX * wY - scalarY * uY)) ∧
    (wY * finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius -
      uY * finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 1 v m probeEnergy broadening disorderStrength hbar pMax radius =
      first * (wY * zX - uY * zY)) := by
  have h :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  dsimp only at h ⊢
  rcases h with ⟨hscalarX, hscalarY, hzX, hzY⟩
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax radius] at
    hscalarX hscalarY hzX hzY
  constructor
  · rw [hscalarX, hscalarY]
    ring
  · rw [hzX, hzY]
    ring

/-- The finite-regulator crossed X trace uses K0/K2 diagonal-current moments and
the K0-K2 recurrence for all four scalar/z crossed-current first harmonics.
The transverse current and scalar/z Green channels retain K0 moments, while
the in-plane Green components use the same K0-K2 reduction. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_harmonic_components
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .x v m probeEnergy broadening disorderStrength hbar pMax radius =
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
      let a :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((aR p * bA p + aA p * bR p) * factor)))
      let b :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              aR p)
      let c :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((-Complex.I * (bR p * dA p - bA p * dR p)) * factor)))
      let d :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              aA p)
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
      let ux := (isotropic + anisotropic) / 2
      let uy :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              ((Complex.I * (aR p * dA p - aA p * dR p)) * factor))
      let uz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((bR p * dA p + bA p * dR p) * factor)))
      let wx := -uy
      let wy := (isotropic - anisotropic) / 2
      let wz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((-Complex.I * (aA p * bR p - aR p * bA p)) * factor)))
      let grx :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                bR p))
      let grz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              dR p)
      let gax :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                bA p))
      let gaz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              dA p)
      2 *
        ((a * b - ux * grx + uz * grz) * (c * d - wx * gax + wz * gaz) +
          (-a * grx + b * ux + Complex.I * uy * grz) *
            (-c * gax + d * wx + Complex.I * wy * gaz) +
          (b * uy - Complex.I * (uz * grx + ux * grz)) *
            (d * wy - Complex.I * (wz * gax + wx * gaz)) +
          (a * grz + b * uz + Complex.I * uy * grx) *
            (c * gaz + d * wz + Complex.I * wy * gax)) := by
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hfirst :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  rcases hdiag with ⟨hxx, hyy⟩
  rcases hfirst with ⟨hscalarX, hscalarY, hzX, hzY⟩
  dsimp only at hxx hyy hscalarX hscalarY hzX hzY
  have htransverse :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRscalar :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRx :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenAscalar :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenAx :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .x .advanced v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenAz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .advanced v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel] at htransverse
  simp only [ite_true] at htransverse
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarKernel] at hGreenRscalar
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at hGreenRx hGreenRz hGreenAx hGreenAz
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarKernel] at hGreenAscalar
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax radius] at hscalarX hscalarY hzX hzY hGreenRx hGreenAx
  simpa only [hxx, hyy, hscalarX, hscalarY, hzX, hzY, htransverse,
    hGreenRscalar, hGreenRx, hGreenRz, hGreenAscalar, hGreenAx, hGreenAz] using
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_x_eq_explicit_pauli_components
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax)

/-- The finite-regulator crossed Psi trace uses explicit K0/K2 diagonal-current
moments and K0-K2 reductions of all first-harmonic current and Green terms.
The transverse K0 current, conjugate partner, and finite regulators remain. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_harmonic_components
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel
        .psi v m probeEnergy broadening disorderStrength hbar pMax radius =
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
      let a :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((aR p * bA p + aA p * bR p) * factor)))
      let b :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              aR p)
      let c := b
      let d :=
        -((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((-Complex.I * (bR p * dA p - bA p * dR p)) * factor))))
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
      let ux := (isotropic + anisotropic) / 2
      let uy :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              ((Complex.I * (aR p * dA p - aA p * dR p)) * factor))
      let uz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((bR p * dA p + bA p * dR p) * factor)))
      let qx := -uy
      let qy := (isotropic - anisotropic) / 2
      let qz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                ((-Complex.I * (aA p * bR p - aR p * bA p)) * factor)))
      let grx :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ((Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2) *
            ∫ p in (0 : ℝ)..pMax,
              (p : ℂ) ^ 2 *
                ((polarFourierZerothAngularKernel (p * radius / hbar) -
                    polarFourierSecondCosineAngularKernel (p * radius / hbar)) *
                bR p))
      let grz :=
        (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
          ∫ p in (0 : ℝ)..pMax,
            (p : ℂ) * (polarFourierZerothAngularKernel (p * radius / hbar) *
              dR p)
      let amplitude :=
        2 *
          ((a * b - ux * grx + uz * grz) * (c * d + grx * qx - grz * qz) +
            (-a * grx + b * ux + Complex.I * uy * grz) *
              (c * qx + d * grx - Complex.I * grz * qy) +
            (b * uy - Complex.I * (uz * grx + ux * grz)) *
              (c * qy + Complex.I * (grz * qx + grx * qz)) +
            (a * grz + b * uz + Complex.I * uy * grx) *
              (-c * qz + d * grz + Complex.I * grx * qy))
      amplitude + (starRingEnd ℂ) amplitude := by
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_diagonal_harmonic_integrals
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hfirst :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_first_harmonic_channels
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  rcases hdiag with ⟨hxx, hyy⟩
  rcases hfirst with ⟨hscalarX, hscalarY, hzX, hzY⟩
  dsimp only at hxx hyy hscalarX hscalarY hzX hzY
  have htransverse :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
      .y 0 v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRscalar :=
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRx :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .x .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  have hGreenRz :=
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
      .z .retarded v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax
  dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel] at htransverse
  simp only [ite_true] at htransverse
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenScalarKernel] at hGreenRscalar
  dsimp only [finiteCutoffContinuumBornDysonRadialGreenPauliKernel] at hGreenRx hGreenRz
  rw [gaussianCrossedRadialFirstHarmonicIntegral_eq_difference hbar pMax radius] at hscalarX hscalarY hzX hzY hGreenRx
  simpa only [hxx, hyy, hscalarX, hscalarY, hzX, hzY, htransverse,
    hGreenRscalar, hGreenRx, hGreenRz] using
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceKernel_psi_eq_explicit_pauli_components
      v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening hdisorder hpMax)

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

end QuantumTheory.Models.MassiveDirac
