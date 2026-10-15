import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRAIntegral
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
    dsimp [q, pref, solved, rx, ry,
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
  obtain ⟨_, hRAEq⟩ := finiteCutoffContinuumBornDysonRAResponse_integrable_and_integral_eq
    1 e v m probeEnergy broadening disorderStrength hbar pMax hbroadening hdisorder.le hpMax
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
  calc
    _ = ∫ p in (0 : ℝ)..pMax,
        -finiteCutoffContinuumBornDysonRAResponseRadialIntegrand
          1 e v m p probeEnergy broadening disorderStrength hbar pMax := by
      apply intervalIntegral.integral_congr
      intro p _
      rw [hpointwise p]
      simp only [finiteCutoffContinuumBornDysonRAResponseRadialIntegrand,
        inPlaneLadderAction_apply_y]
      dsimp [q, pref, solved, rx, ry]
      ring
    _ = -finiteCutoffContinuumBornDysonIntegratedRAResponseVector
        e v m probeEnergy broadening disorderStrength hbar pMax 1 := by
      rw [intervalIntegral.integral_neg, hRAEq]
    _ = _ := by
      simp only [finiteCutoffContinuumBornDysonIntegratedRAResponseVector,
        finiteBroadeningOrderedXYMomentumEndpointForm, Pi.smul_apply, smul_eq_mul]
      ring

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
  have hRA := tendsto_finiteCutoffContinuumBornDysonIntegratedRAResponseVector_broadening_zero
    e regime hrenorm hdet
  rcases regime with ⟨v, m, probeEnergy, disorderStrength, hbar, pMax, hpMax, hvelocity, hhbar,
    hdisorder, hmetal, hcutoff⟩
  have hEndpoint :
      Tendsto
        (fun broadening : ℝ =>
          finiteBroadeningOrderedXYMomentumEndpointForm
            e v m probeEnergy broadening disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)) := by
    simpa only [finiteCutoffContinuumBornDysonIntegratedRAResponseVector,
      finiteCutoffContinuumBornDysonIntegratedRAResponseVectorZeroBroadeningBoundary,
      finiteBroadeningOrderedXYMomentumEndpointForm,
      finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary,
      Pi.smul_apply, smul_eq_mul, neg_mul] using (tendsto_pi_nhds.mp hRA 1).neg
  exact Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    exact (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral_y_eq_endpointForm
      e v m probeEnergy broadening disorderStrength hbar pMax hpMax hhbar
      (ne_of_gt hbroadening) hdisorder).symm) hEndpoint

end

end QuantumTheory.Models.MassiveDirac
