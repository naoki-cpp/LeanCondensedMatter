import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening Born-Dyson ladder

This module propagates the canonical source-`.x` current-rung vector limit through the existing
in-plane ladder algebra. The cutoff remains fixed beyond the metallic shell and the external
broadening has already been removed upstream. No conductivity, ultraviolet, thermodynamic, or
simultaneous limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

private theorem weakDisorderTargetLadderDeterminant_ne_zero
    (m probeEnergy : ℝ) (hmetal : |m| < probeEnergy) :
    inPlaneLadderDeterminant
        (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy : ℂ) 0 ≠ 0 := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : 0 < probeEnergy ^ 2 + 3 * m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have honeReal :
      1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy ≠ 0 := by
    rw [one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy (ne_of_gt hsum)]
    exact div_ne_zero (ne_of_gt hden)
      (mul_ne_zero (by norm_num) (ne_of_gt hsum))
  have honeComplex :
      1 - (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy : ℂ) ≠ 0 := by
    have hcast := Complex.ofReal_ne_zero.mpr honeReal
    simpa using hcast
  simpa [inPlaneLadderDeterminant] using pow_ne_zero 2 honeComplex

private theorem weakDisorderRungLimits
    (v m probeEnergy hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
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
      v m probeEnergy hbar pMax hpMax hvelocity hhbar hmetal hcutoff
  constructor
  · simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung .x
  · simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung .y

/-- The canonical zero-broadening ladder determinant is nonzero for all sufficiently small positive
disorder strengths. -/
theorem eventually_finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary_ne_zero_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    ∀ᶠ disorderStrength : ℝ in nhdsWithin 0 (Set.Ioi 0),
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax ≠ 0 := by
  obtain ⟨hx, hy⟩ :=
    weakDisorderRungLimits
      v m probeEnergy hbar pMax hpMax hvelocity hhbar hmetal hcutoff
  have hOne : Tendsto (fun _ : ℝ => (1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
  have hdiff := hOne.sub hx
  have hdetLimit :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (inPlaneLadderDeterminant
            (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy : ℂ) 0)) := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary,
      inPlaneLadderDeterminant, pow_two] using
      (hdiff.mul hdiff).add (hy.mul hy)
  exact hdetLimit.eventually_ne
    (weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal)

/-- The canonical solved zero-broadening in-plane ladder vector converges to the scalar
weak-disorder fixed point with zero transverse component. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (inPlaneLadderSolvedVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0)) := by
  obtain ⟨hx, hy⟩ :=
    weakDisorderRungLimits
      v m probeEnergy hbar pMax hpMax hvelocity hhbar hmetal hcutoff
  have hdet := weakDisorderTargetLadderDeterminant_ne_zero m probeEnergy hmetal
  simpa [finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary] using
    tendsto_inPlaneLadderSolvedVector hx hy hdet

private theorem weakDisorderTargetLongitudinalLadderAction_eq
    (m probeEnergy : ℝ) (hmetal : |m| < probeEnergy) :
    inPlaneLadderAction
        (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy : ℂ) 0
        (inPlaneLadderSolvedVector
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0) .x =
      (((probeEnergy ^ 2 - m ^ 2) /
        (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ) := by
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : 0 < probeEnergy ^ 2 + m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : 0 < probeEnergy ^ 2 + 3 * m ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have honeReal :
      1 - continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy ≠ 0 := by
    rw [one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy (ne_of_gt hsum)]
    exact div_ne_zero (ne_of_gt hden)
      (mul_ne_zero (by norm_num) (ne_of_gt hsum))
  have honeComplex :
      1 - (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
          m probeEnergy : ℂ) ≠ 0 := by
    have hcast := Complex.ofReal_ne_zero.mpr honeReal
    simpa using hcast
  rw [inPlaneLadderAction_apply_x,
    inPlaneLadderSolvedVector_zero_transverse _ honeComplex]
  simp [inPlaneCoefficientVector]
  have hinvReal :=
    inv_one_sub_continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      m probeEnergy (ne_of_gt hden)
  have hinvCast := congrArg Complex.ofReal hinvReal
  push_cast at hinvCast
  rw [hinvCast]
  unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
  push_cast
  field_simp [ne_of_gt hsum, ne_of_gt hden]
  ring

/-- The longitudinal action of the canonical zero-broadening solved ladder has the explicit
weak-disorder coefficient needed by the downstream scaled Středa conductivity limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalLadderActionZeroBroadeningBoundary_disorder_zero
    (v m probeEnergy hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
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
  obtain ⟨hx, hy⟩ :=
    weakDisorderRungLimits
      v m probeEnergy hbar pMax hpMax hvelocity hhbar hmetal hcutoff
  have hsolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hpMax hvelocity hhbar hmetal hcutoff
  have hsx := tendsto_pi_nhds.mp hsolved .x
  have hsy := tendsto_pi_nhds.mp hsolved .y
  have haction : Tendsto
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
        (inPlaneLadderAction
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ) 0
          (inPlaneLadderSolvedVector
            (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy : ℂ) 0) .x)) := by
    simpa [inPlaneLadderAction_apply_x] using (hx.mul hsx).sub (hy.mul hsy)
  rw [weakDisorderTargetLongitudinalLadderAction_eq m probeEnergy hmetal] at haction
  exact haction

end

end QuantumTheory.Transport.Models.MassiveDirac
