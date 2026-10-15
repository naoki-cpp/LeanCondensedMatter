import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexResponse

set_option linter.style.header false

/-!
# Integrated retarded-advanced current response

This module owns the source-`x` RA response vector before conductivity normalization. It integrates
the current rung acting on the solved ladder vector and transports that complete vector through
the fixed-disorder zero-broadening limit. The disorder-measure prefactor is removed once, leaving
the unnormalized momentum integral with the current factors attached.

The ordered `xy` Středa response consumes the negative transverse projection. The longitudinal
response consumes the longitudinal projection and separately subtracts its bare RR/AA remainder.
These total algebraic values are not an exact disorder average; physical fixed-point interpretation
still requires ladder regularity. No weak-disorder or cutoff limit is taken here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport Filter MeasureTheory
open scoped Interval

/-- Source-`x` RA radial response in the two measured in-plane directions, with current factors but
without conductivity normalization or the same-side remainder. -/
def finiteCutoffContinuumBornDysonRAResponseRadialIntegrand
    (direction : Fin 2) (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  let q : ℂ := ((-e : ℝ) : ℂ) * (v : ℂ)
  2 * q ^ 2 * (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)⁻¹ *
    inPlaneLadderAction
      (fun output => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
        output 0 v m p probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonLadderSolvedVector
        v m probeEnergy broadening disorderStrength hbar pMax) direction

/-- Integrated source-`x` RA response vector, before conductivity normalization and without the
bare RR/AA same-side remainder. -/
def finiteCutoffContinuumBornDysonIntegratedRAResponseVector
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  let q : ℂ := ((-e : ℝ) : ℂ) * (v : ℂ)
  (2 * q ^ 2 * (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)⁻¹) •
    inPlaneLadderAction
      (finiteCutoffContinuumBornDysonCurrentRungVector
        v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonLadderSolvedVector
        v m probeEnergy broadening disorderStrength hbar pMax)

/-- Fixed-disorder zero-broadening value of the complete integrated source-`x` RA response vector. -/
def finiteCutoffContinuumBornDysonIntegratedRAResponseVectorZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  let q : ℂ := ((-e : ℝ) : ℂ) * (v : ℂ)
  (2 * q ^ 2 * (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)⁻¹) •
    inPlaneLadderAction
      (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax)

/-- The RA radial response is integrable and its integral is the corresponding projection of the
integrated vector. The two current-rung entries are integrated together at their response owner. -/
theorem finiteCutoffContinuumBornDysonRAResponse_integrable_and_integral_eq
    (direction : Fin 2) (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    IntervalIntegrable
      (fun p => finiteCutoffContinuumBornDysonRAResponseRadialIntegrand
        direction e v m p probeEnergy broadening disorderStrength hbar pMax) volume 0 pMax ∧
    (∫ p in (0 : ℝ)..pMax, finiteCutoffContinuumBornDysonRAResponseRadialIntegrand
        direction e v m p probeEnergy broadening disorderStrength hbar pMax) =
      finiteCutoffContinuumBornDysonIntegratedRAResponseVector
        e v m probeEnergy broadening disorderStrength hbar pMax direction := by
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
    v m probeEnergy broadening disorderStrength hbar pMax
  let r := fun output p => finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
    output 0 v m p probeEnergy broadening disorderStrength hbar pMax
  have hr (output : Fin 2) : IntervalIntegrable (r output) volume 0 pMax :=
    (continuous_finiteBroadeningBornCurrentRungRadialIntegrand
      output 0 v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax).intervalIntegrable (μ := volume) 0 pMax
  fin_cases direction
  · constructor
    · simp only [finiteCutoffContinuumBornDysonRAResponseRadialIntegrand,
        inPlaneLadderAction_apply_x]
      exact (((hr 0).mul_const (solved 0)).sub ((hr 1).mul_const (solved 1))).const_mul _
    · simp only [finiteCutoffContinuumBornDysonRAResponseRadialIntegrand,
        inPlaneLadderAction_apply_x]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub ((hr 0).mul_const (solved 0))
          ((hr 1).mul_const (solved 1)),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      simp only [finiteCutoffContinuumBornDysonIntegratedRAResponseVector,
        Pi.smul_apply, smul_eq_mul, inPlaneLadderAction_apply_x,
        finiteCutoffContinuumBornDysonCurrentRungVector,
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient]
  · constructor
    · simp only [finiteCutoffContinuumBornDysonRAResponseRadialIntegrand,
        inPlaneLadderAction_apply_y]
      exact (((hr 1).mul_const (solved 0)).add ((hr 0).mul_const (solved 1))).const_mul _
    · simp only [finiteCutoffContinuumBornDysonRAResponseRadialIntegrand,
        inPlaneLadderAction_apply_y]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hr 1).mul_const (solved 0))
          ((hr 0).mul_const (solved 1)),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      simp only [finiteCutoffContinuumBornDysonIntegratedRAResponseVector,
        Pi.smul_apply, smul_eq_mul, inPlaneLadderAction_apply_y,
        finiteCutoffContinuumBornDysonCurrentRungVector,
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient]

/-- At fixed positive disorder and finite cutoff, the complete integrated RA response converges
before either physical response projects a direction or adds its same-side contribution. -/
theorem tendsto_finiteCutoffContinuumBornDysonIntegratedRAResponseVector_broadening_zero
    (e : ℝ) (regime : FixedCutoffMetallicBornRegime)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    Tendsto
      (fun broadening => finiteCutoffContinuumBornDysonIntegratedRAResponseVector
        e regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar regime.pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteCutoffContinuumBornDysonIntegratedRAResponseVectorZeroBroadeningBoundary
        e regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax)) := by
  have hAction := tendsto_inPlaneLadderAction
    (tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm)
    (tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm hdet)
  exact hAction.const_smul _

end

end QuantumTheory.Models.MassiveDirac
