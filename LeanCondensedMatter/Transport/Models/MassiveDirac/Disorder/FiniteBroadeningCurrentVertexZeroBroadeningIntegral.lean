import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadening
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening limit of the finite-cutoff Born-Dyson current-rung radial integrals

The pointwise fixed-radial-momentum `η → 0⁺` limits are owned upstream by
`FiniteBroadeningCurrentVertexZeroBroadening`.  This module records the exact dominated-convergence
boundary needed to pass that limit through the normalized finite radial current-rung integrals.

The cutoff and disorder strength remain fixed.  No weak-disorder, ultraviolet, solved-ladder,
conductivity, or simultaneous-limit statement is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

/-- Zero-broadening boundary of the normalized finite-cutoff longitudinal current-rung coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

/-- Zero-broadening boundary of the normalized finite-cutoff orientation-sensitive current-rung
coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
      v m p probeEnergy disorderStrength hbar pMax

/-- Dominated convergence passes `η → 0⁺` through the normalized finite radial longitudinal rung
integral once one integrable radial bound, eventual strong measurability, and nonvanishing of the
boundary RA denominator on the compact radial interval are supplied. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient_broadening_zero_of_dominated
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (bound : ℝ → ℝ)
    (hMeasurable :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (fun p =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
          (volume.restrict (Set.Icc 0 pMax)))
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc 0 pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hpointwise :
      ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
        Tendsto
          (fun broadening : ℝ =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
              v m p probeEnergy disorderStrength hbar pMax)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand_broadening_zero
        v m p probeEnergy disorderStrength hbar pMax
        hvelocity hmetal hcutoff (hden p hp))
  have hset := tendsto_integral_filter_of_dominated_convergence
    bound hMeasurable hBound hBoundIntegrable hpointwise
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficient
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialXIntegrandZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungXCoefficientZeroBroadeningBoundary
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hfinite, hboundary]
  exact hset

/-- Dominated convergence passes `η → 0⁺` through the normalized finite radial orientation-sensitive
rung integral under the same compact denominator-regularity and domination hypotheses. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient_broadening_zero_of_dominated
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax)
    (hvelocity : v ≠ 0) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hden : ∀ p ∈ Set.Icc (0 : ℝ) pMax,
      finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProductZeroBroadeningBoundary
        v m p probeEnergy disorderStrength hbar pMax ≠ 0)
    (bound : ℝ → ℝ)
    (hMeasurable :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        AEStronglyMeasurable
          (fun p =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
          (volume.restrict (Set.Icc 0 pMax)))
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc 0 pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hpointwise :
      ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
        Tendsto
          (fun broadening : ℝ =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
              v m p probeEnergy broadening disorderStrength hbar pMax)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
              v m p probeEnergy disorderStrength hbar pMax)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand_broadening_zero
        v m p probeEnergy disorderStrength hbar pMax
        hvelocity hmetal hcutoff (hden p hp))
  have hset := tendsto_integral_filter_of_dominated_convergence
    bound hMeasurable hBound hBoundIntegrable hpointwise
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrand
            v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficient
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialYIntegrandZeroBroadeningBoundary
            v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungYCoefficientZeroBroadeningBoundary
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hfinite, hboundary]
  exact hset

end

end QuantumTheory.Transport.Models.MassiveDirac
