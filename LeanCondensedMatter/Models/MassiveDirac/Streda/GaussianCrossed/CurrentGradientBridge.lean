import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpace
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVResolventDifference
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Spectral-difference bridge for physical Gaussian-crossed current kernels

The actual finite-cutoff source-x current block is built from a retarded and
an advanced Born-Dyson Green function. Its scalar and Pauli-z first-angular
harmonics are two-resolvent terms. These can be converted **exactly** into
the difference of the corresponding single resolvents using the common
spectral gap

  Δ = (E_A² - M_A²) - (E_R² - M_R²).

No narrow-width approximation, replacement of running Born parameters,
or cutoff removal is made here. In particular these identities are
multiplied by Δ: division by Δ and a weak-disorder limit would require
additional hypotheses and estimates.

The remaining Pauli-x and Pauli-y harmonics are *not* identified with
a Green difference here; Eq. (14) of Ado et al. is a leading-order,
matrix-valued result, not an exact finite-broadening assertion.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The physical retarded/advanced Born-Dyson quadratic spectral gap.
It is independent of the radial momentum, even though each Dyson
spectral parameter depends on the fixed Born reference cutoff. -/
noncomputable def finiteCutoffContinuumBornDysonRASpectralGap
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax ^ 2) -
  (finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax ^ 2)

/-- The *physical* RA two-resolvent radial weight is the spectral
difference of single Dyson resolvents. This equation stays valid even
if the spectral gap itself vanishes, because it is not divided out. -/
theorem finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    (v m probeEnergy broadening disorderStrength hbar pMax p : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      ((finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
       (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) =
      (finiteCutoffContinuumBornDysonDenominator
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
      (finiteCutoffContinuumBornDysonDenominator
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ := by
  let eR : ℂ := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let eA : ℂ := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let mR : ℂ := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let mA : ℂ := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let sR : ℂ := eR ^ 2 - mR ^ 2
  let sA : ℂ := eA ^ 2 - mA ^ 2
  let q : ℂ := ((v ^ 2 * p ^ 2 : ℝ) : ℂ)
  have hR : sR - q ≠ 0 := by
    simpa [sR, q, eR, mR, finiteCutoffContinuumBornDysonDenominator] using
      (finiteCutoffContinuumBornDysonDenominator_ne_zero
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax)
  have hA : sA - q ≠ 0 := by
    simpa [sA, q, eA, mA, finiteCutoffContinuumBornDysonDenominator] using
      (finiteCutoffContinuumBornDysonDenominator_ne_zero
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder hpMax)
  simpa [finiteCutoffContinuumBornDysonRASpectralGap,
    finiteCutoffContinuumBornDysonDenominator, sR, sA, q, eR, eA, mR, mA] using
    (massiveDiracUnitResolvent_inverse_sub sR sA q hR hA).symm

/-- Exact source-x scalar current-kernel bridge: after multiplying by
the physical RA spectral gap, the two-propagator first harmonic becomes
the *difference* of retarded and advanced one-propagator harmonics.

This is already a concrete kernel of the X/Psi current blocks, not a
reference Bessel integral or an independently postulated current. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedScalarKernel_gap_eq
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let dR := finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel
        0 v m probeEnergy broadening disorderStrength hbar pMax radius p =
      ((p : ℂ) ^ 2) *
        polarFourierFirstCosineAngularKernel (p * radius / hbar) *
        ((v : ℂ) * (eR + eA)) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax *
        (dR⁻¹ - dA⁻¹) := by
  dsimp only
  have hgap := finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    v m probeEnergy broadening disorderStrength hbar pMax p
    hbroadening hdisorder hpMax
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarKernel,
    finiteCutoffContinuumBornDysonRadialPauliData,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]
  rw [← hgap]
  push_cast
  ring

/-- The source-x Pauli-z crossed current has the *same* RA
spectral-difference structure, with the sum of effective masses in
place of the sum of effective energies. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedZKernel_gap_eq
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let dR := finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
    let dA := finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius p =
      ((p : ℂ) ^ 2) *
        polarFourierFirstCosineAngularKernel (p * radius / hbar) *
        ((v : ℂ) * (mR + mA)) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax *
        (dR⁻¹ - dA⁻¹) := by
  dsimp only
  have hgap := finiteCutoffContinuumBornDysonRASpectralGap_mul_inv_product
    v m probeEnergy broadening disorderStrength hbar pMax p
    hbroadening hdisorder hpMax
  simp only [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliKernel,
    finiteCutoffContinuumBornDysonRadialPauliData,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent]
  rw [← hgap]
  push_cast
  ring

/-- The physical RA first-harmonic *difference moment*, with exactly
one radial physical momentum measure. It is the derivative kernel of
the R/A scalar Fourier-generator difference (before the explicit
derivative identification), not an independent reference Bessel model. -/
noncomputable def finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ((p : ℂ) ^ 2) *
        polarFourierFirstCosineAngularKernel (p * radius / hbar) *
        ((finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
         (finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹)

/-- Lift a pointwise spectral-gap identity to an *integrated physical*
radial current coefficient. The same regulated radial measure appears
on both sides, and no improper-limit interchange is used. -/
private theorem massiveDiracRASpectralGap_mul_integral
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (weight : ℂ) (kernel : ℝ → ℂ)
    (hpoint : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRASpectralGap
          v m probeEnergy broadening disorderStrength hbar pMax * kernel p =
        weight * (((p : ℂ) ^ 2) *
          polarFourierFirstCosineAngularKernel (p * radius / hbar) *
          ((finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
           (finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹))) :
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      ((((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax, kernel p) =
      weight * finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
        v m probeEnergy broadening disorderStrength hbar pMax radius := by
  unfold finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
  calc
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (finiteCutoffContinuumBornDysonRASpectralGap
            v m probeEnergy broadening disorderStrength hbar pMax *
          (∫ p in (0 : ℝ)..pMax, kernel p)) := by ring
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRASpectralGap
            v m probeEnergy broadening disorderStrength hbar pMax * kernel p) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        (∫ p in (0 : ℝ)..pMax,
          weight * (((p : ℂ) ^ 2) *
            polarFourierFirstCosineAngularKernel (p * radius / hbar) *
            ((finiteCutoffContinuumBornDysonDenominator
              .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
             (finiteCutoffContinuumBornDysonDenominator
              .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹))) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro p _
      exact hpoint p
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      ring

/-- An actual integrated source-x scalar crossed-current coefficient
is a scalar multiple of the R/A first-harmonic difference moment.
This eliminates the two-resolvent product from that physical channel. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedScalarCurrent_gap_eq
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient
        0 v m probeEnergy broadening disorderStrength hbar pMax radius =
      ((v : ℂ) * (eR + eA) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax) *
      finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
        v m probeEnergy broadening disorderStrength hbar pMax radius := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentScalarCoefficient_eq_radialKernel_integral
    0 v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  apply massiveDiracRASpectralGap_mul_integral
  intro p
  have h := finiteCutoffContinuumBornDysonGaussianCrossedScalarKernel_gap_eq
    v m probeEnergy broadening disorderStrength hbar pMax radius p
    hbroadening hdisorder hpMax
  dsimp only at h
  calc
    _ = ((p : ℂ) ^ 2) *
          polarFourierFirstCosineAngularKernel (p * radius / hbar) *
          ((v : ℂ) *
            (finiteCutoffContinuumBornEffectiveEnergy .retarded v m probeEnergy
              broadening disorderStrength hbar pMax +
             finiteCutoffContinuumBornEffectiveEnergy .advanced v m probeEnergy
              broadening disorderStrength hbar pMax)) *
          finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
            v m probeEnergy broadening disorderStrength hbar pMax *
          ((finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
           (finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := h
    _ = _ := by ring

/-- The real-space source-x Pauli-z crossed current obeys the same
integrated identity, with the sum of effective R/A masses. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedZCurrent_gap_eq
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonRASpectralGap
        v m probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient
        .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius =
      ((v : ℂ) * (mR + mA) *
        finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
          v m probeEnergy broadening disorderStrength hbar pMax) *
      finiteCutoffContinuumBornDysonRAFirstHarmonicDifferenceMoment
        v m probeEnergy broadening disorderStrength hbar pMax radius := by
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_eq_radialKernel_integral
    .z 0 v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  apply massiveDiracRASpectralGap_mul_integral
  intro p
  have h := finiteCutoffContinuumBornDysonGaussianCrossedZKernel_gap_eq
    v m probeEnergy broadening disorderStrength hbar pMax radius p
    hbroadening hdisorder hpMax
  dsimp only at h
  calc
    _ = ((p : ℂ) ^ 2) *
          polarFourierFirstCosineAngularKernel (p * radius / hbar) *
          ((v : ℂ) *
            (finiteCutoffContinuumBornEffectiveMass .retarded v m probeEnergy
              broadening disorderStrength hbar pMax +
             finiteCutoffContinuumBornEffectiveMass .advanced v m probeEnergy
              broadening disorderStrength hbar pMax)) *
          finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
            v m probeEnergy broadening disorderStrength hbar pMax *
          ((finiteCutoffContinuumBornDysonDenominator
            .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ -
           (finiteCutoffContinuumBornDysonDenominator
            .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹) := h
    _ = _ := by ring

end

end QuantumTheory.Models.MassiveDirac
