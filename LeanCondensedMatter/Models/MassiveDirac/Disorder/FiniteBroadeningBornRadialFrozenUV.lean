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

This module also owns the clean (zero-disorder) diagonal-cutoff existence
results, using the explicit fixed-spectral Fourier UV boundary rather than
an independent low-momentum/tail existence proof.
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
    massiveDiracRadialFourierUVCenter v (radius / hbar) (energy ^ 2 - mass ^ 2)

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
      energy ^ 2 - mass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0 := by
    change massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pRef)
        (finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pRef) ≠ 0
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pRef
      hbroadening hdisorder hpRef
  have hlimit := massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
    v (radius / hbar)
    (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2))
    (energy ^ 2 - mass ^ 2) hv (div_ne_zero hradius hhbar) hden le_rfl
  have hpoint (outer : ℝ) :
      (∫ p in (0 : ℝ)..outer,
        (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
          (finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pRef)⁻¹) =
      (∫ p in (0 : ℝ)..outer,
        (p : ℂ) * polarFourierZerothAngularKernel (p * (radius / hbar)) *
          (energy ^ 2 - mass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [show p * radius / hbar = p * (radius / hbar) by ring]
    rw [show energy ^ 2 - mass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) =
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pRef from by
      simpa only [massiveDiracRadialDenominator] using
        (finiteCutoffContinuumBornDysonDenominator_eq_radial
          side v m p probeEnergy broadening disorderStrength hbar pRef)]
  have hphysical := hlimit.congr'
    (Filter.Eventually.of_forall fun outer => (hpoint outer).symm)
  change Filter.Tendsto
    (fun outer : ℝ => (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      (∫ p in (0 : ℝ)..outer,
        (p : ℂ) * polarFourierZerothAngularKernel (p * radius / hbar) *
          (finiteCutoffContinuumBornDysonDenominator
            side v m p 0 probeEnergy broadening disorderStrength hbar pRef)⁻¹))
    Filter.atTop
    (nhds ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
      massiveDiracRadialFourierUVFinitePartCenter v (radius / hbar)
        (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)) (energy ^ 2 - mass ^ 2)))
  exact hphysical.const_mul (((momentumMeasurePrefactor hbar : ℝ) : ℂ))


/-- Explicit zero-disorder diagonal UV value of the physical scalar generator.
The Born self-energy vanishes, so the outer momentum cutoff can be taken
without a running-self-energy limit. The physical momentum measure occurs once. -/
noncomputable def finiteCutoffContinuumBornDysonRadialScalarCleanUVValue
    (side : SpectralSide)
    (v m probeEnergy broadening hbar radius : ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    massiveDiracRadialFourierUVCenter v (radius / hbar)
      ((spectralParameter side probeEnergy broadening) ^ 2 - (m : ℂ) ^ 2)

/-- On the clean (`disorderStrength = 0`) slice, the *actual* finite-cutoff
radial scalar Green generator converges to the explicit spectral-center Fourier UV value when its Born and outer momentum
cutoffs increase together. This is a diagonal cutoff limit, unlike the
frozen-self-energy statement above: the dependence on `pMax` disappears
because the Born self-energy vanishes identically.

The conclusion is for nonzero real-space Fourier scale `radius / hbar`
and nonzero external broadening. It makes no claim for finite disorder. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_zero_disorder_tendsto_uvValue
    (side : SpectralSide)
    (v m probeEnergy broadening hbar radius : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hradius : radius ≠ 0)
    (hbroadening : broadening ≠ 0) :
    Filter.Tendsto
      (fun pMax : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening 0 hbar pMax radius)
      Filter.atTop
        (nhds (finiteCutoffContinuumBornDysonRadialScalarCleanUVValue
          side v m probeEnergy broadening hbar radius)) := by
  have hden (p : ℝ) :
      massiveDiracRadialDenominator v p
        (spectralParameter side probeEnergy broadening) (m : ℂ) ≠ 0 := by
    have hphysical := finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening 0 hbar 0
      hbroadening (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    rw [← finiteCutoffContinuumBornDysonDenominator_eq_radial] at hphysical
    simpa [finiteCutoffContinuumBornEffectiveEnergy,
      finiteCutoffContinuumBornEffectiveMass] using hphysical
  have hlimit := massiveDiracRadialFourier_tendsto_uvFinitePartAt
    v (radius / hbar)
    (max (1 : ℝ)
      (2 * ‖(spectralParameter side probeEnergy broadening) ^ 2 -
        (m : ℂ) ^ 2‖ / v ^ 2))
    (spectralParameter side probeEnergy broadening) (m : ℂ)
    hv (div_ne_zero hradius hhbar) hden le_rfl
  have heq (pMax : ℝ) :
      finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening 0 hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) * polarFourierZerothAngularKernel (p * (radius / hbar)) *
            (massiveDiracRadialDenominator v p
              (spectralParameter side probeEnergy broadening) (m : ℂ))⁻¹ := by
    unfold finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    congr 1
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [← finiteCutoffContinuumBornDysonDenominator_eq_radial]
    simp only [finiteCutoffContinuumBornEffectiveEnergy,
      finiteCutoffContinuumBornEffectiveMass,
      finiteCutoffContinuumBornSelfEnergyCoefficient_zero_disorder,
      sub_zero, add_zero]
    rw [show p * radius / hbar = p * (radius / hbar) by ring]
    ring
  have hscaled := hlimit.const_mul (((momentumMeasurePrefactor hbar : ℝ) : ℂ))
  unfold finiteCutoffContinuumBornDysonRadialScalarCleanUVValue massiveDiracRadialFourierUVCenter
  exact hscaled.congr'
    (Filter.Eventually.of_forall fun pMax => (heq pMax).symm)


/-- Compatibility: the explicitly identified clean UV limit supplies
the previous existential diagonal-cutoff theorem without a second
radial convergence proof. -/
theorem finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_zero_disorder_tendsto_atTop
    (side : SpectralSide)
    (v m probeEnergy broadening hbar radius : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hradius : radius ≠ 0)
    (hbroadening : broadening ≠ 0) :
    ∃ value : ℂ, Filter.Tendsto
      (fun pMax : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
        side v m probeEnergy broadening 0 hbar pMax radius)
      Filter.atTop (nhds value) := by
  exact ⟨finiteCutoffContinuumBornDysonRadialScalarCleanUVValue
      side v m probeEnergy broadening hbar radius,
    finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_zero_disorder_tendsto_uvValue
      side v m probeEnergy broadening hbar radius hv hhbar hradius hbroadening⟩


/-- The clean diagonal ultraviolet limit of the common scalar generator
also controls the **physical** identity and z-Pauli coefficients of the
radial Green matrix. Both limits share the same generator limit and retain
the effective-energy/mass factors, which become the bare spectral center
and mass when the Born disorder strength is zero.

The in-plane derivative coefficient is not included: differentiating
an infinite-cutoff limit requires separate uniform estimates. -/
theorem finiteCutoffContinuumBornDysonRadialGreenScalarZ_zero_disorder_tendsto_atTop
    (side : SpectralSide)
    (v m probeEnergy broadening hbar radius : ℝ)
    (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hradius : radius ≠ 0)
    (hbroadening : broadening ≠ 0) :
    ∃ value : ℂ,
      Filter.Tendsto
        (fun pMax : ℝ => finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
          side v m probeEnergy broadening 0 hbar pMax radius)
        Filter.atTop (nhds (spectralParameter side probeEnergy broadening * value)) ∧
      Filter.Tendsto
        (fun pMax : ℝ => finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .z
          side v m probeEnergy broadening 0 hbar pMax radius)
        Filter.atTop (nhds ((m : ℂ) * value)) := by
  obtain ⟨value, hlimit⟩ :=
    finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_zero_disorder_tendsto_atTop
      side v m probeEnergy broadening hbar radius hv hhbar hradius hbroadening
  refine ⟨value, ?_, ?_⟩
  · have hscaled : Filter.Tendsto
        (fun pMax : ℝ => spectralParameter side probeEnergy broadening *
          finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            side v m probeEnergy broadening 0 hbar pMax radius)
        Filter.atTop (nhds (spectralParameter side probeEnergy broadening * value)) :=
      tendsto_const_nhds.mul hlimit
    apply hscaled.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with pMax hpMax
    rw [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_generator
      side v m probeEnergy broadening 0 hbar pMax radius
      hbroadening (le_refl (0 : ℝ)) hpMax]
    simp [finiteCutoffContinuumBornEffectiveEnergy]
  · have hscaled : Filter.Tendsto
        (fun pMax : ℝ => (m : ℂ) *
          finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
            side v m probeEnergy broadening 0 hbar pMax radius)
        Filter.atTop (nhds ((m : ℂ) * value)) :=
      tendsto_const_nhds.mul hlimit
    apply hscaled.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with pMax hpMax
    rw [finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_z_eq_generator
      side v m probeEnergy broadening 0 hbar pMax radius
      hbroadening (le_refl (0 : ℝ)) hpMax]
    simp [finiteCutoffContinuumBornEffectiveMass]

end

end QuantumTheory.Models.MassiveDirac
