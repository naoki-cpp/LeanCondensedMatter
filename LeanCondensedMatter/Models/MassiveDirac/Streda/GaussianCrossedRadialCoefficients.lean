import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial Pauli coefficient integration bridges

The massive-Dirac radial Green and Gaussian-crossed current Pauli coefficients equal the physical
momentum-measure prefactor times integrals of their canonical pointwise radial kernels.
Entrywise interval-integrability follows from the finite-broadening, finite-cutoff model.
This module does not define crossed X/Psi topologies or evaluate their traces.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport

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

/-- In the finite-broadening finite-cutoff regime, the radial Green scalar coefficient is the momentum
measure prefactor times the integral of its explicit pointwise Pauli scalar kernel. -/
theorem finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_radialKernel_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenScalarKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  have hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax := by
    intro i j
    exact intervalIntegrable_finiteCutoffContinuumBornDysonRadialGreenEntryKernel
      side v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax i j
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

/-- In the finite-broadening finite-cutoff regime, every radial Green Pauli component is the momentum
measure prefactor times the integral of its explicit pointwise Pauli-vector kernel. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_radialKernel_integral
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        axis side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenPauliKernel
            axis side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  have hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax := by
    intro i j
    exact intervalIntegrable_finiteCutoffContinuumBornDysonRadialGreenEntryKernel
      side v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax i j
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

/-- In the finite-broadening finite-cutoff regime, the radial Gaussian-crossed current scalar
coefficient is the momentum-measure prefactor times the integral of its explicit pointwise
Pauli scalar kernel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        source v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel
            source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  have hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax := by
    intro i j
    exact intervalIntegrable_finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
      source v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax i j
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

/-- In the finite-broadening finite-cutoff regime, every radial Gaussian-crossed current Pauli component
is the momentum-measure prefactor times the integral of its explicit pointwise Pauli-vector
kernel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
    (axis : PauliAxis) (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        axis source v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
            axis source v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  have hentry : ∀ i j, IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      volume 0 pMax := by
    intro i j
    exact intervalIntegrable_finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
      source v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax i j
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


end

end QuantumTheory.Models.MassiveDirac
