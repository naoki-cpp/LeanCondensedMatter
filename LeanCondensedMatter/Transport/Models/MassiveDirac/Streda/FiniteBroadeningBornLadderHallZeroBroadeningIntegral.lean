import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.TransportDomain
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening ordered transverse Středa radial integral

For the ordered measured-`x`, source-`y` component, the isotropic same-side `RR/AA` contribution
vanishes after angular reduction. The remaining finite-cutoff Středa momentum integral can therefore
be reduced directly to the transverse component of the canonical integrated Born current rung acting on the
solved in-plane ladder vector. This avoids introducing a second dominated-convergence argument at the
Středa layer.

The disorder strength and cutoff remain fixed. The result is the ordered `xy` Středa momentum-integral
response component; physical conductivity normalization and Hall projection remain downstream. No
weak-disorder, ultraviolet, thermodynamic, or simultaneous limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory QuantumTheory.Transport
open scoped Interval

private def finiteBroadeningOrderedXYMomentumEndpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let rung := finiteCutoffContinuumBornDysonCurrentRungVector
    v m probeEnergy broadening disorderStrength hbar pMax
  (-2 : ℂ) * q ^ 2 * pref⁻¹ * inPlaneLadderAction rung solved 1

/-- Fixed-disorder zero-broadening boundary of the ordered `xy` Středa momentum integral. -/
def finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  (-2 : ℂ) * q ^ 2 * pref⁻¹ * inPlaneLadderAction rung solved 1

private theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_y_eq_endpointForm
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 < disorderStrength) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
        0 1 e v m probeEnergy broadening disorderStrength hbar pMax =
      finiteBroadeningOrderedXYMomentumEndpointForm
        e v m probeEnergy broadening disorderStrength hbar pMax := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let pref : ℂ :=
    (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let rx : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      0 0 v m p probeEnergy broadening disorderStrength hbar pMax
  let ry : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      1 0 v m p probeEnergy broadening disorderStrength hbar pMax
  have hpref : pref ≠ 0 := by
    dsimp [pref, continuumBornDisorderMeasurePrefactor, momentumMeasurePrefactor]
    exact_mod_cast mul_ne_zero (ne_of_gt hdisorder)
      (one_div_ne_zero (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)))
  have hpointwise : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 1 e v m p probeEnergy broadening disorderStrength hbar pMax =
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * (solved 1 * rx p + solved 0 * ry p) := by
    intro p
    rw [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm]
    dsimp [q, pref, solved, rx, ry]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
    dsimp only
    have hprefEq :
        (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ) = pref := by
      rfl
    rw [hprefEq]
    have hdenp :
        finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
          v m p probeEnergy broadening disorderStrength hbar pMax ≠ 0 :=
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_ne_zero
        v m p probeEnergy broadening disorderStrength hbar pMax
        hbroadening hdisorder.le hpMax
    field_simp [hpref, hdenp]
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
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  have hintegral :
      (∫ p in (0 : ℝ)..pMax,
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 1 e v m p probeEnergy broadening disorderStrength hbar pMax) =
      ∫ p in (0 : ℝ)..pMax,
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * (solved 1 * rx p + solved 0 * ry p) := by
    apply intervalIntegral.integral_congr
    intro p _
    exact hpointwise p
  rw [hintegral]
  change
    (∫ p in (0 : ℝ)..pMax,
      (((-2 : ℂ) * q ^ 2 * pref⁻¹) • (solved 1 * rx p + solved 0 * ry p))) =
      finiteBroadeningOrderedXYMomentumEndpointForm
        e v m probeEnergy broadening disorderStrength hbar pMax
  rw [intervalIntegral.integral_smul]
  rw [intervalIntegral.integral_add
    (hrx.const_mul (solved 1)) (hry.const_mul (solved 0)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient,
    finiteCutoffContinuumBornDysonCurrentRungVector,
    finiteBroadeningOrderedXYMomentumEndpointForm, inPlaneLadderAction_apply_y,
    q, pref, solved, rx, ry]
  all_goals ring_nf
  all_goals simp

/-- At fixed positive disorder and finite cutoff, the ordered `xy` Středa momentum integral converges
to its zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegral_broadening_zero
    (e : ℝ) (regime : FixedCutoffMetallicBornRegime)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
          0 1 e regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar
          regime.pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
          e regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax)) := by
  have hRung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm
  rcases regime with ⟨v, m, probeEnergy, disorderStrength, hbar, pMax, hpMax, hvelocity, hhbar,
    hdisorder, hmetal, hcutoff⟩
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  have hAction := tendsto_inPlaneLadderAction hRung hSolved
  have hEndpoint :
      Tendsto
        (fun broadening : ℝ =>
          finiteBroadeningOrderedXYMomentumEndpointForm
            e v m probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)) := by
    simpa only [finiteBroadeningOrderedXYMomentumEndpointForm,
      finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary] using
      (tendsto_pi_nhds.mp hAction 1).const_mul
        (((-2 : ℂ) * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
          (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)⁻¹))
  exact Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_y_eq_endpointForm
      e v m probeEnergy broadening disorderStrength hbar pMax hpMax hhbar
      (ne_of_gt hbroadening) hdisorder).symm) hEndpoint

end

end QuantumTheory.Transport.Models.MassiveDirac
