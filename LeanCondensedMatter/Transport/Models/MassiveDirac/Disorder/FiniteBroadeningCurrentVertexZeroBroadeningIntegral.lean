import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadening
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zero-broadening limit of finite-cutoff Born-Dyson current-rung radial integrals

The fixed-radial-momentum `η → 0⁺` limits are owned upstream by
`FiniteBroadeningCurrentVertexZeroBroadening`. This module records the dominated-convergence
boundary needed to pass that limit through any direction-indexed normalized radial current-rung
entry.

The cutoff and disorder strength remain fixed. No weak-disorder, ultraviolet, solved-ladder,
conductivity, or simultaneous-limit statement is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

/-- Zero-broadening boundary of normalized finite-cutoff current-rung entry `(i,j)`. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
      i j v m p probeEnergy disorderStrength hbar pMax

/-- Dominated convergence passes `η → 0⁺` through any normalized finite radial current-rung entry
once one integrable radial bound, eventual strong measurability, and nonvanishing of the boundary RA
denominator on the compact radial interval are supplied. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_dominated
    (i j : Direction2)
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
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax)
          (volume.restrict (Set.Icc 0 pMax)))
    (hBound :
      ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
          ‖finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax‖ ≤ bound p)
    (hBoundIntegrable : Integrable bound (volume.restrict (Set.Icc 0 pMax))) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax)) := by
  have hpointwise :
      ∀ᵐ p ∂(volume.restrict (Set.Icc 0 pMax)),
        Tendsto
          (fun broadening : ℝ =>
            finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
              i j v m p probeEnergy broadening disorderStrength hbar pMax)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
              i j v m p probeEnergy disorderStrength hbar pMax)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun p hp =>
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand_broadening_zero
        i j v m p probeEnergy disorderStrength hbar pMax
        hvelocity hmetal hcutoff (hden p hp))
  have hset := tendsto_integral_filter_of_dominated_convergence
    bound hMeasurable hBound hBoundIntegrable hpointwise
  have hfinite :
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
          i j v m probeEnergy broadening disorderStrength hbar pMax) =
      (fun broadening : ℝ =>
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrand
            i j v m p probeEnergy broadening disorderStrength hbar pMax) := by
    funext broadening
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hboundary :
      finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          i j v m probeEnergy disorderStrength hbar pMax =
        ∫ p in Set.Icc (0 : ℝ) pMax,
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungRadialIntegrandZeroBroadeningBoundary
            i j v m p probeEnergy disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
    rw [intervalIntegral.integral_of_le hpMax]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hfinite, hboundary]
  exact hset

end

end QuantumTheory.Transport.Models.MassiveDirac
