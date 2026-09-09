import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening Born-Dyson ladder

The source-`.x` rung-vector limit is propagated directly through the generic in-plane ladder API.
The cutoff remains fixed beyond the metallic shell. No conductivity, ultraviolet, thermodynamic, or
simultaneous limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

private theorem weakDisorderTargetOneMinusRung_ne_zero
    (m probeEnergy : ℝ) (hmetal : |m| < probeEnergy) :
    1 - (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy : ℂ) ≠ 0 := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : 0 < probeEnergy ^ 2 + 3 * m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hreal :
      1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy ≠ 0 := by
    rw [one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy (ne_of_gt hsum)]
    exact div_ne_zero (ne_of_gt hden)
      (mul_ne_zero (by norm_num) (ne_of_gt hsum))
  simpa using Complex.ofReal_ne_zero.mpr hreal

private theorem weakDisorderTargetLadderDeterminant_ne_zero
    (m probeEnergy : ℝ) (hmetal : |m| < probeEnergy) :
    inPlaneLadderDeterminant
        (inPlaneCoefficientVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0) ≠ 0 := by
  simpa [inPlaneLadderDeterminant, inPlaneCoefficientVector] using
    pow_ne_zero 2 (weakDisorderTargetOneMinusRung_ne_zero m probeEnergy hmetal)

/-- The canonical zero-broadening ladder determinant is nonzero for all sufficiently small positive
disorder strengths. -/
theorem eventually_finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary_ne_zero_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    ∀ᶠ disorderStrength : ℝ in nhdsWithin 0 (Set.Ioi 0),
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax ≠ 0 := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hdet := tendsto_inPlaneLadderDeterminant hrung
  simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using
    hdet.eventually_ne (weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal)

/-- The longitudinal action of the canonical zero-broadening solved ladder has the explicit
weak-disorder coefficient needed by the downstream scaled Středa conductivity limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalLadderActionZeroBroadeningBoundary_disorder_zero
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
            v m probeEnergy disorderStrength hbar pMax) .x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ)) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  let κ : ℂ := continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    m probeEnergy
  let targetRung := inPlaneCoefficientVector κ 0
  have hdet := weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal
  have hsolved :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inPlaneLadderSolvedVector targetRung)) := by
    simpa [finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary,
      targetRung, κ] using tendsto_inPlaneLadderSolvedVector hrung hdet
  have haction := tendsto_inPlaneLadderAction hrung hsolved
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      inPlaneLadderAction targetRung (inPlaneLadderSolvedVector targetRung) .x =
        (((probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ) := by
    rw [inPlaneLadderAction_apply_x,
      inPlaneLadderSolvedVector_zero_transverse κ
        (by simpa [κ] using weakDisorderTargetOneMinusRung_ne_zero m probeEnergy hmetal)]
    simp only [targetRung, inPlaneCoefficientVector, zero_mul, sub_zero, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    have hreal :
        continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient m probeEnergy *
            (1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy)⁻¹ =
          (probeEnergy ^ 2 - m ^ 2) / (probeEnergy ^ 2 + 3 * m ^ 2) := by
      rw [inv_one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
        m probeEnergy hden]
      unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      field_simp [hsum, hden]
    have hrealCast := congrArg Complex.ofReal hreal
    push_cast at hrealCast
    simpa [κ] using hrealCast
  have hactionX := tendsto_pi_nhds.mp haction .x
  rw [htarget] at hactionX
  exact hactionX

end

end QuantumTheory.Transport.Models.MassiveDirac
