import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVFinitePart
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility

set_option linter.style.header false

/-!
# Explicit radial UV value at a frozen physical Born cutoff

The physical Born-Dyson spectral energy and mass at a **fixed** disorder
cutoff pRef are complex constants with respect to the *separate* outer
Fourier momentum cutoff. At nonzero broadening and nonnegative scalar
disorder, the proven invertibility of the Born-Dyson propagator excludes
real radial poles, so the explicit finite-part limit theorem applies.

The new result identifies the outer-UV boundary of the *actual physical*
Born-Dyson Fourier kernel with its momentum normalization, not merely
an existential limit. It is not the diagonal limit pRef = outer -> ∞:
at nonzero disorder the unrenormalized Born spectral parameters
diverge, so the latter needs additional counterterms and uniform
estimates. It does not evaluate the crossed X conductivity.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- Canonical, fully specified UV value for the scalar radial Green
Fourier transform with the physical Born self-energy frozen at pRef.
The physical factor `momentumMeasurePrefactor hbar` occurs exactly once.
The low-K0/high-K1 split is an auxiliary analytic device. -/
noncomputable def finiteCutoffContinuumBornDysonRadialFrozenUVValue
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pRef radius : ℝ) : ℂ :=
  let energy := finiteCutoffContinuumBornEffectiveEnergy
    side v m probeEnergy broadening disorderStrength hbar pRef
  let mass := finiteCutoffContinuumBornEffectiveMass
    side v m probeEnergy broadening disorderStrength hbar pRef
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    massiveDiracRadialFourierUVValue v (radius / hbar) energy mass

/-- At a frozen physical Born cutoff, the exact scalar Fourier Green
kernel converges to an **explicit** UV finite-part expression,
including its momentum measure. No `η -> 0`, `W -> 0`, self-energy
UV limit, or radial cutoff limit is taken. -/
theorem finiteCutoffContinuumBornDysonRadialFrozenKernel_tendsto_uvValue
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pRef radius : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hradius : radius ≠ 0)
    (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpRef : 0 ≤ pRef) :
    Filter.Tendsto
      (fun outer : ℝ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..outer,
          (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pRef)⁻¹)
      Filter.atTop (nhds
        (finiteCutoffContinuumBornDysonRadialFrozenUVValue
          side v m probeEnergy broadening disorderStrength hbar pRef radius)) := by
  let energy := finiteCutoffContinuumBornEffectiveEnergy
    side v m probeEnergy broadening disorderStrength hbar pRef
  let mass := finiteCutoffContinuumBornEffectiveMass
    side v m probeEnergy broadening disorderStrength hbar pRef
  have hden (p : ℝ) :
      massiveDiracRadialDenominator v p energy mass ≠ 0 := by
    change massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pRef)
        (finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pRef) ≠ 0
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pRef
      hbroadening hdisorder hpRef
  have hlimit := massiveDiracRadialFourier_tendsto_uvFinitePartAt
    v (radius / hbar)
    (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2))
    energy mass hv (div_ne_zero hradius hhbar) hden le_rfl
  have hscaled := hlimit.const_mul (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
  have hpoint (outer : ℝ) :
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (∫ p in (0 : ℝ)..outer,
          (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
            (finiteCutoffContinuumBornDysonDenominator
              side v m p 0 probeEnergy broadening disorderStrength hbar pRef)⁻¹) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (∫ p in (0 : ℝ)..outer,
          (p : ℂ) * polarFourierZerothAngularKernel (p * (radius / hbar)) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹) := by
    apply congrArg (fun z : ℂ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) * z)
    apply intervalIntegral.integral_congr
    intro p _
    rw [show p * radius / hbar = p * (radius / hbar) by ring]
    rw [show massiveDiracRadialDenominator v p energy mass =
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pRef from
      finiteCutoffContinuumBornDysonDenominator_eq_radial
        side v m p probeEnergy broadening disorderStrength hbar pRef]
  change Filter.Tendsto
    (fun outer : ℝ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      (∫ p in (0 : ℝ)..outer,
        (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
          (finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pRef)⁻¹))
    Filter.atTop
    (nhds ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      massiveDiracRadialFourierUVFinitePartAt v (radius / hbar)
        (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)) energy mass))
  exact hscaled.congr' (Filter.Eventually.of_forall fun outer => (hpoint outer).symm)

end

end QuantumTheory.Models.MassiveDirac
