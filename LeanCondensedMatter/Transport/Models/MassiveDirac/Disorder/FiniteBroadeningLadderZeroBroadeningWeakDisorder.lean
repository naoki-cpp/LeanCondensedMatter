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
        (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy : ℂ) 0 ≠ 0 := by
  simpa [inPlaneLadderDeterminant] using
    pow_ne_zero 2 (weakDisorderTargetOneMinusRung_ne_zero m probeEnergy hmetal)

private theorem weakDisorderRungLimits
    (v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
            .x .x v m probeEnergy disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ)) ∧
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
            .y .x v m probeEnergy disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  exact ⟨by simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung .x,
    by simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung .y⟩

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
  obtain ⟨hx, hy⟩ := weakDisorderRungLimits
    v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  exact (tendsto_inPlaneLadderDeterminant hx hy).eventually_ne
    (weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal)

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
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
            .x .x v m probeEnergy disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
            .y .x v m probeEnergy disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax) .x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ)) := by
  obtain ⟨hx, hy⟩ := weakDisorderRungLimits
    v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  let κ : ℂ := continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
    m probeEnergy
  have hdet := weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal
  have hsolved :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inPlaneLadderSolvedVector κ 0)) := by
    simpa [κ, finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary] using
      tendsto_inPlaneLadderSolvedVector hx hy hdet
  have haction :=
    (hx.mul (tendsto_pi_nhds.mp hsolved .x)).sub
      (hy.mul (tendsto_pi_nhds.mp hsolved .y))
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      inPlaneLadderAction κ 0 (inPlaneLadderSolvedVector κ 0) .x =
        (((probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ) := by
    rw [inPlaneLadderAction_apply_x,
      inPlaneLadderSolvedVector_zero_transverse κ
        (by simpa [κ] using weakDisorderTargetOneMinusRung_ne_zero m probeEnergy hmetal)]
    simp [inPlaneCoefficientVector]
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
  have htarget' :
      κ * (inPlaneLadderSolvedVector κ 0) Direction2.x -
          0 * (inPlaneLadderSolvedVector κ 0) Direction2.y =
        (((probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ) := by
    simpa [inPlaneLadderAction_apply_x] using htarget
  rw [htarget'] at haction
  simpa [inPlaneLadderAction_apply_x] using haction

end

end QuantumTheory.Transport.Models.MassiveDirac
