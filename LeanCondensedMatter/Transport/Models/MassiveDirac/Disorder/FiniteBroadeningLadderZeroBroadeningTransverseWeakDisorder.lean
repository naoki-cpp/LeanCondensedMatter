import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningTransverseWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scaled transverse weak-disorder limit of the zero-broadening ladder

This module propagates the first nonvanishing transverse current-rung coefficient through the
canonical two-component solved ladder. The quotient by `W` is formed before the one-sided
weak-disorder limit, so the orientation-sensitive term needed by the ordered Hall response is not
lost when the raw transverse rung tends to zero.

The cutoff remains fixed beyond the metallic shell. No Středa insertion, conductivity normalization,
Hall projection, ultraviolet limit, or simultaneous broadening/disorder limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- At fixed cutoff beyond the metallic shell, the transverse action of the zero-broadening solved
ladder divided by `W` has a finite one-sided weak-disorder limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonTransverseLadderActionZeroBroadeningBoundary_div_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        inPlaneLadderAction
            (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
              v m probeEnergy disorderStrength hbar pMax)
            (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
              v m probeEnergy disorderStrength hbar pMax) .y /
          (disorderStrength : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
          (probeEnergy ^ 2 + m ^ 2) /
          (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ))) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let rung := fun disorderStrength : ℝ =>
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax
  let κ : ℝ := continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    m probeEnergy
  let targetRung : InPlaneCoefficientVector := inPlaneCoefficientVector (κ : ℂ) 0
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : 0 < probeEnergy ^ 2 + 3 * m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hrung : Tendsto rung l (nhds targetRung) := by
    simpa [rung, l, targetRung, κ] using
      tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
        v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hOneMinus :
      1 - κ = (probeEnergy ^ 2 + 3 * m ^ 2) /
        (2 * (probeEnergy ^ 2 + m ^ 2)) := by
    dsimp [κ]
    exact one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy (ne_of_gt hsum)
  have hκ : 1 - κ ≠ 0 := by
    rw [hOneMinus]
    exact div_ne_zero (ne_of_gt hden)
      (mul_ne_zero (by norm_num) (ne_of_gt hsum))
  have hκC : (1 : ℂ) - (κ : ℂ) ≠ 0 := by
    exact_mod_cast hκ
  have hdet0 : inPlaneLadderDeterminant targetRung ≠ 0 := by
    simpa [targetRung, inPlaneLadderDeterminant, inPlaneCoefficientVector] using
      pow_ne_zero 2 hκC
  have hdet := tendsto_inPlaneLadderDeterminant hrung
  have hslope :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_y_div_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hclosed := hslope.mul (hdet.inv₀ hdet0)
  have hdetEq :
      inPlaneLadderDeterminant targetRung =
        (((((probeEnergy ^ 2 + 3 * m ^ 2) /
          (2 * (probeEnergy ^ 2 + m ^ 2))) ^ 2 : ℝ) : ℂ)) := by
    dsimp [targetRung]
    simp only [inPlaneLadderDeterminant, inPlaneCoefficientVector, add_zero]
    have hOneMinusC :
        (1 : ℂ) - (κ : ℂ) =
          ((((probeEnergy ^ 2 + 3 * m ^ 2) /
            (2 * (probeEnergy ^ 2 + m ^ 2)) : ℝ) : ℂ)) := by
      exact_mod_cast hOneMinus
    rw [hOneMinusC]
    norm_num
  have htargetReal :
      (Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
          (v ^ 2 * (probeEnergy ^ 2 + m ^ 2))) *
          (((probeEnergy ^ 2 + 3 * m ^ 2) /
            (2 * (probeEnergy ^ 2 + m ^ 2))) ^ 2)⁻¹ =
        4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
          (probeEnergy ^ 2 + m ^ 2) /
          (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) := by
    field_simp [hvelocity, ne_of_gt hsum, ne_of_gt hden]
    ring
  have htarget :
      (((Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
          (v ^ 2 * (probeEnergy ^ 2 + m ^ 2)) : ℝ) : ℂ)) *
          (inPlaneLadderDeterminant targetRung)⁻¹ =
        (((4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
          (probeEnergy ^ 2 + m ^ 2) /
          (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) := by
    rw [hdetEq]
    exact_mod_cast htargetReal
  rw [htarget] at hclosed
  apply Tendsto.congr' ?_ hclosed
  filter_upwards with disorderStrength
  simp only [finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary]
  rw [inPlaneLadderAction_apply_y]
  simp only [inPlaneLadderSolvedVector_apply_x, inPlaneLadderSolvedVector_apply_y]
  dsimp [rung]
  field_simp
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
