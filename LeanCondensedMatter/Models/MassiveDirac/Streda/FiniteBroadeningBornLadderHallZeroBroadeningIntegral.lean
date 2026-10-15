import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Models.MassiveDirac.TransportDomain
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

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

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
  let radialRung : ℝ → InPlaneCoefficientVector := fun p output =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
      output 0 v m p probeEnergy broadening disorderStrength hbar pMax
  have hpref : pref ≠ 0 := by
    dsimp [pref, continuumBornDisorderMeasurePrefactor, momentumMeasurePrefactor]
    exact_mod_cast mul_ne_zero (ne_of_gt hdisorder)
      (one_div_ne_zero (pow_ne_zero 2
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar)))
  have hpointwise : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
          0 1 e v m p probeEnergy broadening disorderStrength hbar pMax =
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * inPlaneLadderAction (radialRung p) solved 1 := by
    intro p
    rw [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand_eq_denominatorForm]
    simp only [inPlaneLadderAction_apply_y]
    dsimp [q, pref, solved, radialRung,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector]
    rw [finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm,
      finiteCutoffContinuumBornDysonRetardedAdvancedAngularCoefficient_eq_denominatorForm]
    unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialNumerator
    dsimp only
    simp only [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      Matrix.transpose_apply, inPlaneRotationMatrix_apply_x_x,
      inPlaneRotationMatrix_apply_y_x]
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
  have hRadialRung (output : Fin 2) :
      IntervalIntegrable (fun p => radialRung p output) volume 0 pMax :=
    (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
      output 0 v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder.le hpMax).intervalIntegrable (μ := volume) 0 pMax
  obtain ⟨_, hActionEq⟩ := inPlaneLadderAction_integrable_and_integral_eq
    radialRung solved 0 pMax hRadialRung 1
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  calc
    _ = (-2 : ℂ) * q ^ 2 * pref⁻¹ *
        ∫ p in (0 : ℝ)..pMax, inPlaneLadderAction (radialRung p) solved 1 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro p _
      exact hpointwise p
    _ = _ := by
      simpa only [q, pref, solved, radialRung, finiteBroadeningOrderedXYMomentumEndpointForm,
        finiteCutoffContinuumBornDysonCurrentRungVector,
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient] using
        congrArg (fun z : ℂ => (-2 : ℂ) * q ^ 2 * pref⁻¹ * z) hActionEq

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
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm hdet
  rcases regime with ⟨v, m, probeEnergy, disorderStrength, hbar, pMax, hpMax, hvelocity, hhbar,
    hdisorder, hmetal, hcutoff⟩
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

end QuantumTheory.Models.MassiveDirac
