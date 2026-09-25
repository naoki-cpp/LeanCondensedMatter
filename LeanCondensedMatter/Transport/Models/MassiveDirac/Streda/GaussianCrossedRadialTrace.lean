import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial Gaussian crossed trace kernels

This module reduces the model-specific finite-cutoff Gaussian crossed `X` / `Psi` trace kernels to
one-dimensional radial Green and current blocks on the real-space radial axis. The canonical
topology still contains `r ↦ -r`, but the massive-Dirac Green/current inversion laws eliminate
negative-radius blocks from the scalar entry-sum and radial-kernel evaluation boundaries.

The radial specialization reuses the canonical topology from `GaussianCrossedTrace`; it does not
redefine the `X` / `Psi` matrix products. The two radial topologies are additionally exposed as
finite scalar sums over matrix entries and then as products of one-dimensional scalar momentum
integrals. No real-space angular integration, cutoff removal, broadening/disorder limit, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

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

private theorem pauliScalarCoefficient_prefactor_intervalIntegral
    (kernel : ℝ → Matrix2) (prefactor : ℂ) (a b : ℝ)
    (hkernel : ∀ i j, IntervalIntegrable (fun p => kernel p i j) volume a b) :
    (prefactor * (∫ p in a..b, kernel p 0 0) +
        prefactor * (∫ p in a..b, kernel p 1 1)) / 2 =
      prefactor * ∫ p in a..b, InternalSpace.pauliScalarCoefficient (kernel p) := by
  simp only [InternalSpace.pauliScalarCoefficient]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hkernel 0 0) (hkernel 1 1)]
  ring

private theorem pauliVectorCoefficient_prefactor_intervalIntegral
    (axis : PauliAxis) (kernel : ℝ → Matrix2) (prefactor : ℂ) (a b : ℝ)
    (hkernel : ∀ i j, IntervalIntegrable (fun p => kernel p i j) volume a b) :
    (match axis with
      | .x =>
          (prefactor * (∫ p in a..b, kernel p 0 1) +
            prefactor * (∫ p in a..b, kernel p 1 0)) / 2
      | .y =>
          Complex.I *
            (prefactor * (∫ p in a..b, kernel p 0 1) -
              prefactor * (∫ p in a..b, kernel p 1 0)) / 2
      | .z =>
          (prefactor * (∫ p in a..b, kernel p 0 0) -
            prefactor * (∫ p in a..b, kernel p 1 1)) / 2) =
      prefactor * ∫ p in a..b, InternalSpace.pauliVectorCoefficient (kernel p) axis := by
  cases axis
  · simp only [InternalSpace.pauliVectorCoefficient]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add (hkernel 0 1) (hkernel 1 0)]
    ring
  · simp only [InternalSpace.pauliVectorCoefficient]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hkernel 0 1) (hkernel 1 0)]
    ring
  · simp only [InternalSpace.pauliVectorCoefficient]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hkernel 0 0) (hkernel 1 1)]
    ring

/-- Under entrywise interval-integrability, the radial Green scalar coefficient is the momentum
measure prefactor times the integral of its explicit pointwise Pauli scalar kernel. -/
theorem finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax) :
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenScalarKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  rw [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_entryKernel_integrals]
  rw [pauliScalarCoefficient_prefactor_intervalIntegral
    (kernel := fun p i j => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
      side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
    (hkernel := hentry)]
  apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
  apply intervalIntegral.integral_congr
  intro p _
  exact finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliScalarCoefficient
    side v m probeEnergy broadening disorderStrength hbar pMax radius p

/-- Under entrywise interval-integrability, every radial Green Pauli component is the momentum
measure prefactor times the integral of its explicit pointwise Pauli-vector kernel. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax) :
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        axis side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenPauliKernel
            axis side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  rw [finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_entryKernel_integrals]
  cases axis with
  | x =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .x)
      (kernel := fun p i j => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliVectorCoefficient
      .x side v m probeEnergy broadening disorderStrength hbar pMax radius p
  | y =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .y)
      (kernel := fun p i j => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliVectorCoefficient
      .y side v m probeEnergy broadening disorderStrength hbar pMax radius p
  | z =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .z)
      (kernel := fun p i j => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliVectorCoefficient
      .z side v m probeEnergy broadening disorderStrength hbar pMax radius p

/-- Under entrywise interval-integrability, the radial Gaussian-crossed current scalar
coefficient is the momentum-measure prefactor times the integral of its explicit pointwise
Pauli scalar kernel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        source v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_entryKernel_integrals]
  rw [pauliScalarCoefficient_prefactor_intervalIntegral
    (kernel := fun p i j => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
      source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
    (hkernel := hentry)]
  apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
  apply intervalIntegral.integral_congr
  intro p _
  exact finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliScalarCoefficient
    source v m probeEnergy broadening disorderStrength hbar pMax radius p

/-- Under entrywise interval-integrability, every radial Gaussian-crossed current Pauli component
is the momentum-measure prefactor times the integral of its explicit pointwise Pauli-vector
kernel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        axis source v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            axis source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_entryKernel_integrals]
  cases axis with
  | x =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .x)
      (kernel := fun p i j =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
          source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
        .x source v m probeEnergy broadening disorderStrength hbar pMax radius p
  | y =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .y)
      (kernel := fun p i j =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
          source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
        .y source v m probeEnergy broadening disorderStrength hbar pMax radius p
  | z =>
    simp only
    have hmove := pauliVectorCoefficient_prefactor_intervalIntegral
      (axis := .z)
      (kernel := fun p i j =>
        finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
          source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (a := 0) (b := pMax) (hkernel := hentry)
    simp only at hmove
    rw [hmove]
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    exact
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
        .z source v m probeEnergy broadening disorderStrength hbar pMax radius p

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
