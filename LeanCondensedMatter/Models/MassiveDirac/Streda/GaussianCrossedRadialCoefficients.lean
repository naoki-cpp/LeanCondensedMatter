import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial Pauli coefficient integration bridges

The Gaussian-crossed current Pauli coefficients equal the physical
momentum-measure prefactor times integrals of their canonical pointwise radial kernels.
Entrywise interval-integrability follows from the finite-broadening, finite-cutoff model.
The Green coefficient integration laws belong to
`Disorder.FiniteBroadeningBornRadialRealSpacePropagator`; the common Pauli integration laws belong
to `Analysis.InternalSpace.Pauli`. This module does not define crossed X/Psi topologies or evaluate
their traces.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport

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
  trans (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax, InternalSpace.pauliScalarCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p)
  · exact InternalSpace.pauliScalarCoefficient_prefactor_intervalIntegral
      (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
      (kernel := fun p i j => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      (hkernel := hentry)
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
  have hmove := InternalSpace.pauliVectorCoefficient_prefactor_intervalIntegral
    (axis := axis)
    (prefactor := (((momentumMeasurePrefactor hbar : ℝ) : ℂ)))
    (kernel := fun p i j => finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
      source v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
    (hkernel := hentry)
  trans (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax, InternalSpace.pauliVectorCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel
        source v m probeEnergy broadening disorderStrength hbar pMax radius p) axis
  · cases axis <;> exact hmove
  apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
  apply intervalIntegral.integral_congr
  intro p _
  exact finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentEntryKernel_pauliVectorCoefficient
    axis source v m probeEnergy broadening disorderStrength hbar pMax radius p


end

end QuantumTheory.Models.MassiveDirac
