import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.ScalarGenerator
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.QuadraticKernel

set_option linter.style.header false

/-!
# Born-Dyson specialization of the quadratic radial Fourier tail identity

Only the finite-regulator Born-Dyson denominator specialization is owned here. The
model-independent derivative, integration-by-parts and UV-limit results live in
`Propagator.RadialFourier.QuadraticKernel`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open PolarRadialKernels
open MeasureTheory
open scoped Interval

/-- The finite-broadening Born-Dyson scalar Fourier kernel inherits the
exact ultraviolet integration-by-parts identity with the *physical*
retarded/advanced complex effective energy and mass, before any cutoff
or broadening limit. -/
theorem finiteCutoffContinuumBornDysonRadialScalarKernel_by_parts
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax c a b : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let D := fun p : ℝ => finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    (Complex.I * (c : ℂ)) *
        (∫ p in a..b, (p : ℂ) *
          polarFourierZerothAngularKernel (p * c) * (D p)⁻¹) =
      ((b : ℂ) * polarFourierFirstCosineAngularKernel (b * c) * (D b)⁻¹) -
      ((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) * (D a)⁻¹) -
      (∫ p in a..b,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) * (D p)⁻¹ ^ 2)) := by
  have hden (p : ℝ) :
      massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hcenter (p : ℝ) :
      (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax) ^ 2 -
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax) ^ 2 -
      ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [massiveDiracRadialDenominator] using hden p
  have h := integral_massiveDiracRadialCenter_inv_fourierKernel_by_parts
    v c a b
    ((finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax) ^ 2 -
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax) ^ 2)
    hcenter
  dsimp only
  simpa only [← finiteCutoffContinuumBornDysonDenominator_eq_radial,
    massiveDiracRadialDenominator] using h

end

end QuantumTheory.Models.MassiveDirac
