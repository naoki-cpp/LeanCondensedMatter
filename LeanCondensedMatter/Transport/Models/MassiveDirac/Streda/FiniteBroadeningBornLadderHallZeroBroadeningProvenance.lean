import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Provenance expansion of the zero-broadening ordered transverse Středa endpoint

The ordered `xy` zero-broadening endpoint is built from the transverse component of the canonical
in-plane ladder action. In the repository `Gᴿ Γ Gᴬ` orientation that component is exactly

```text
r_y Γ_x + r_x Γ_y,
```

where `r` is the integrated current rung and `Γ` is the solved dressed-current vector. The canonical
object remains `inPlaneLadderAction`; this module only exposes theorem-level provenance expansions
and their one-sided weak-disorder limits. No second public representation of the ladder action is
introduced.

The cutoff remains fixed beyond the metallic shell. Conductivity normalization, Hall projection,
mechanism classification, crossed diagrams, ultraviolet removal, and simultaneous limits remain
downstream.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The completed ordered `xy` zero-broadening Středa momentum endpoint is exactly the sum of the
two concrete products already present in the `y` component of the canonical in-plane ladder action.
This records algebraic provenance only; it is not a scattering-mechanism decomposition. -/
theorem finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_eq_rungSolvedProvenance
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
    let pref : ℂ :=
      (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
    let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax
    let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax
    finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
        e v m probeEnergy disorderStrength hbar pMax =
      (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 1 * solved 0) +
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 0 * solved 1) := by
  simp [finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary,
    inPlaneLadderAction_apply_y]
  ring

private theorem tendsto_orderedXYProvenance_rungYSolvedX_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
        let pref : ℂ :=
          (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
        let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 1 * solved 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hmeasureReal : momentumMeasurePrefactor hbar ≠ 0 := by
    unfold momentumMeasurePrefactor
    exact one_div_ne_zero (pow_ne_zero 2
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))
  have hmeasure : measure ≠ 0 := by
    dsimp [measure]
    exact_mod_cast hmeasureReal
  have hslope :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_y_div_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hsolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hsolvedX :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (((2 * (probeEnergy ^ 2 + m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) := by
    simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hsolved (0 : Fin 2)
  have hscaled := (hslope.mul hsolvedX).const_mul ((-2 : ℂ) * q ^ 2 * measure⁻¹)
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htargetReal :
      (-2 : ℝ) * ((-e) * v) ^ 2 * (momentumMeasurePrefactor hbar)⁻¹ *
          ((Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
            (v ^ 2 * (probeEnergy ^ 2 + m ^ 2))) *
            (2 * (probeEnergy ^ 2 + m ^ 2) /
              (probeEnergy ^ 2 + 3 * m ^ 2))) =
        -8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
          (probeEnergy ^ 2 + 3 * m ^ 2) := by
    unfold continuumBornAngularMeasurePrefactor
    (field_simp [hvelocity, hmeasureReal, hsum, hden]; ring)
  have htargetCast := congrArg Complex.ofReal htargetReal
  push_cast at htargetCast
  have htarget :
      ((-2 : ℂ) * q ^ 2 * measure⁻¹) *
          ((((Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m /
            (v ^ 2 * (probeEnergy ^ 2 + m ^ 2)) : ℝ) : ℂ)) *
            (((2 * (probeEnergy ^ 2 + m ^ 2) /
              (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) =
        (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
          (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ)) := by
    simpa [q, measure] using htargetCast
  rw [htarget] at hscaled
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  dsimp [q, measure, continuumBornDisorderMeasurePrefactor]
  push_cast
  field_simp [hdisorderC, hmeasure]

private theorem tendsto_orderedXYProvenance_rungXSolvedY_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
        let pref : ℂ :=
          (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
        let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        (-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 0 * solved 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
          (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ))) := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hmeasureReal : momentumMeasurePrefactor hbar ≠ 0 := by
    unfold momentumMeasurePrefactor
    exact one_div_ne_zero (pow_ne_zero 2
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))
  have hmeasure : measure ≠ 0 := by
    dsimp [measure]
    exact_mod_cast hmeasureReal
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hrungX :
      Tendsto
        (fun disorderStrength : ℝ =>
          finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
            v m probeEnergy disorderStrength hbar pMax 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
            m probeEnergy : ℂ)) := by
    simpa [inPlaneCoefficientVector] using tendsto_pi_nhds.mp hrung (0 : Fin 2)
  have hsolvedSlope :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary_y_div_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hscaled := (hrungX.mul hsolvedSlope).const_mul ((-2 : ℂ) * q ^ 2 * measure⁻¹)
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hsum : probeEnergy ^ 2 + m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htargetReal :
      (-2 : ℝ) * ((-e) * v) ^ 2 * (momentumMeasurePrefactor hbar)⁻¹ *
          (continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy *
            (4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
              (probeEnergy ^ 2 + m ^ 2) /
              (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))) =
        -8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
          (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 := by
    unfold continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
      continuumBornAngularMeasurePrefactor
    (field_simp [hvelocity, hmeasureReal, hsum, hden]; ring)
  have htargetCast := congrArg Complex.ofReal htargetReal
  push_cast at htargetCast
  have htarget :
      ((-2 : ℂ) * q ^ 2 * measure⁻¹) *
          ((continuumBornRetardedAdvancedPauliXWeakDisorderCurrentRungCoefficient
              m probeEnergy : ℂ) *
            (((4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
              (probeEnergy ^ 2 + m ^ 2) /
              (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ))) =
        (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
          (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)) := by
    simpa [q, measure] using htargetCast
  rw [htarget] at hscaled
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  dsimp [q, measure, continuumBornDisorderMeasurePrefactor]
  push_cast
  field_simp [hdisorderC, hmeasure]

/-- The two concrete products in the ordered-`xy` ladder-action expansion have a joint finite
one-sided weak-disorder limit. The temporary vector is only a theorem-level packaging of the two
provenance terms: component `0` is `r_y Γ_x`, component `1` is `r_x Γ_y`. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRungSolvedProvenance_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
        let pref : ℂ :=
          (continuumBornDisorderMeasurePrefactor disorderStrength hbar : ℂ)
        let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        let rung := finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax
        inPlaneCoefficientVector
          ((-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 1 * solved 0))
          ((-2 : ℂ) * q ^ 2 * pref⁻¹ * (rung 0 * solved 1)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (inPlaneCoefficientVector
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))
          (((-8 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
            (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)))) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [inPlaneCoefficientVector] using
      tendsto_orderedXYProvenance_rungYSolvedX_disorder_zero
        e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  · simpa [inPlaneCoefficientVector] using
      tendsto_orderedXYProvenance_rungXSolvedY_disorder_zero
        e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff

end

end QuantumTheory.Transport.Models.MassiveDirac
