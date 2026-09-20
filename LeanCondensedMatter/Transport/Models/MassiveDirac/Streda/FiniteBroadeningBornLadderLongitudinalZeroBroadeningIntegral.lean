import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalSameSide
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening longitudinal Středa radial integral

The ordered measured-`x`, source-`x` response composes the integrated RA current rung with the
canonical same-side RR/AA radial remainder. This gives its fixed-disorder `η → 0⁺` boundary without
a second Středa DCT layer or reopening the same-side endpoint analysis.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private def finiteBroadeningLongitudinalMomentumEndpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let rung := finiteCutoffContinuumBornDysonCurrentRungVector
    v m probeEnergy broadening disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * inPlaneLadderAction rung solved 0 -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (finiteBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy broadening disorderStrength hbar pMax +
        finiteBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy broadening disorderStrength hbar pMax)

/-- Fixed-disorder zero-broadening boundary of the canonical longitudinal Středa momentum integral. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  2 * q ^ 2 * pref⁻¹ * inPlaneLadderAction rung solved 0 -
    (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
      (zeroBroadeningSameSideRadialEndpoint
          .retarded v m probeEnergy disorderStrength hbar pMax +
        zeroBroadeningSameSideRadialEndpoint
          .advanced v m probeEnergy disorderStrength hbar pMax)

private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_x_eq_endpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 0 e v m probeEnergy broadening disorderStrength hbar pMax =
      finiteBroadeningLongitudinalMomentumEndpointForm
        e v m probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let rx : ℝ → ℂ := fun p => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    0 0 v m p probeEnergy broadening disorderStrength hbar pMax
  let ry : ℝ → ℂ := fun p => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    1 0 v m p probeEnergy broadening disorderStrength hbar pMax
  let same : SpectralSide → ℝ → ℂ := fun side p =>
    (p : ℂ) * (finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ ^ 2 *
      (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
        finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax ^ 2)
  have hpref : pref ≠ 0 := by
    dsimp [pref, continuumBornDisorderMeasurePrefactor, momentumMeasurePrefactor]
    exact_mod_cast mul_ne_zero (ne_of_gt hdisorder)
      (one_div_ne_zero (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)))
  have hpointwise : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 0 e v m p probeEnergy broadening disorderStrength hbar pMax =
        2 * q ^ 2 * pref⁻¹ * (solved 0 * rx p - solved 1 * ry p) -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 * (same .retarded p + same .advanced p) := by
    intro p
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand_eq_radialCoefficient,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceRadialCoefficient_x_eq_denominatorForm]
    dsimp [q, solved, rx, ry, same]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    simp only [finiteCutoffContinuumBornDysonRetardedAdvancedAngularNumerator,
      inPlaneRotationMatrix_apply_x_x, inPlaneRotationMatrix_apply_y_x,
      inPlaneCoefficientVector]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul, mul_inv_rev]
    have hprefEq :
        (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ) = pref := by
      rfl
    rw [hprefEq]
    set dRinv : ℂ :=
      (finiteCutoffContinuumBornDysonDenominator
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
    set dAinv : ℂ :=
      (finiteCutoffContinuumBornDysonDenominator
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹
    field_simp [hpref]
    all_goals push_cast
    all_goals ring_nf
  have hrx : IntervalIntegrable rx volume 0 pMax := by
    simpa [rx] using
      (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
        0 0 v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax).intervalIntegrable (μ := volume) 0 pMax
  have hry : IntervalIntegrable ry volume 0 pMax := by
    simpa [ry] using
      (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
        1 0 v m probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax).intervalIntegrable (μ := volume) 0 pMax
  obtain ⟨hrr, hrrEq⟩ := finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder.le hpMax
  obtain ⟨haa, haaEq⟩ := finiteBroadeningSameSide_integrable_and_integral_eq_endpoint
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
    hvelocity hbroadening hdisorder.le hpMax
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  have hintegral :
      (∫ p in (0 : ℝ)..pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 0 e v m p probeEnergy broadening disorderStrength hbar pMax) =
      ∫ p in (0 : ℝ)..pMax,
        2 * q ^ 2 * pref⁻¹ * (solved 0 * rx p - solved 1 * ry p) -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 * (same .retarded p + same .advanced p) := by
    apply intervalIntegral.integral_congr
    intro p _
    exact hpointwise p
  rw [hintegral]
  rw [intervalIntegral.integral_sub
    (((hrx.const_mul (solved 0)).sub (hry.const_mul (solved 1))).const_mul
      (2 * q ^ 2 * pref⁻¹))
    ((hrr.add haa).const_mul ((((2 * Real.pi : ℝ) : ℂ)) * q ^ 2))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hrx.const_mul (solved 0)) (hry.const_mul (solved 1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hrr haa]
  rw [show (∫ p in (0 : ℝ)..pMax, same .retarded p) = finiteBroadeningSameSideRadialEndpoint
      .retarded v m probeEnergy broadening disorderStrength hbar pMax by simpa [same] using hrrEq]
  rw [show (∫ p in (0 : ℝ)..pMax, same .advanced p) = finiteBroadeningSameSideRadialEndpoint
      .advanced v m probeEnergy broadening disorderStrength hbar pMax by simpa [same] using haaEq]
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient,
    finiteCutoffContinuumBornDysonCurrentRungVector,
    finiteBroadeningLongitudinalMomentumEndpointForm, inPlaneLadderAction_apply_x,
    q, pref, solved, rx, ry]
  all_goals ring_nf
  all_goals simp

/-- At fixed positive disorder and finite cutoff, the canonical longitudinal Středa momentum
integral converges directly to its zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral_broadening_zero
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ => finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 0 e v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax)) := by
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hRung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm
  have hAction := tendsto_inPlaneLadderAction hRung hSolved
  have hden (side : SpectralSide) (p : ℝ) :=
    finiteCutoffContinuumBornDysonDenominatorZeroBroadeningBoundary_ne_zero
      side v m p probeEnergy disorderStrength hbar pMax
      hvelocity hhbar hdisorder hmetal hrenorm
  have hRR := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .retarded v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden .retarded 0) (hden .retarded pMax)
  have hAA := tendsto_finiteBroadeningSameSideRadialEndpoint_broadening_zero
    .advanced v m probeEnergy disorderStrength hbar pMax hvelocity hmetal hcutoff
    (hden .advanced 0) (hden .advanced pMax)
  have htotal :=
    ((tendsto_pi_nhds.mp hAction 0).const_mul
      (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
        (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)⁻¹)).sub
    ((hRR.add hAA).const_mul
      ((((2 * Real.pi : ℝ) : ℂ)) * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2))
  have hEndpoint :
      Tendsto
        (fun broadening : ℝ =>
          finiteBroadeningLongitudinalMomentumEndpointForm
            e v m probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)) := by
    simpa [finiteBroadeningLongitudinalMomentumEndpointForm,
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary] using htotal
  exact Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_x_eq_endpointForm
      e v m probeEnergy broadening disorderStrength hbar pMax hpMax hvelocity hhbar
      (ne_of_gt hbroadening) hdisorder).symm) hEndpoint

end

end QuantumTheory.Transport.Models.MassiveDirac
